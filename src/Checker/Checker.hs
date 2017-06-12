{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Checker.Checker where

import Syntax.Expr
import Syntax.Pretty
import Checker.Types
import Checker.Environment
import Prelude hiding (pred)

import Data.List
import Data.Maybe
import Control.Monad.State.Strict
import Control.Monad.Reader.Class
import Control.Monad.Trans.Maybe
import Data.SBV hiding (kindOf)
import Debug.Trace

-- Checking (top-level)
check :: [Def]        -- List of definitions
      -> Bool         -- Debugging flag
      -> [(Id, Id)]   -- Name map
      -> IO (Either String Bool)
check defs dbg nameMap = do
    -- Compute the common coeffect used in the program
    -- TODO: get rid of this and allow mixing of coeffects in one file
    let globalCKind  = foldr kindJoin CPoly (map (\(Def _ _ _ ty) -> tyCoeffectKind ty) defs)

    -- Initial state for the checker
    let initialState = CS 0 ground globalCKind
    -- Build the computation to check all the defs (in order)...
    let checkedDefs = foldM checkDef ([], empty) defs
    -- ... and evaluate the computation with initial state
    (results, _) <- evalChecker initialState nameMap checkedDefs

    -- If all definitions type checkerd, then the whole file type checkers
    if (and . map (\(_, _, _, checked) -> isJust checked) $ results)
      then return . Right $ True
      -- Otherwise, show the checking reports
      else return . Left  $ intercalate "\n" (map mkReport results)
  where
    ground = return (true, [])

    checkDef (results, def_env) (Def var expr _ ty) = do
      addAnyUniversalsTy ty
      env' <- runMaybeT $ do
               -- (v, pred, k) <- get
               -- put (v, pred, tyCoeffectKind ty)
               env' <- checkExpr dbg def_env [] ty expr
               solved <- solveConstraints
               if solved
                 then return ()
                 else illTyped "Constraints violated"
               return env'
      -- synth attempt to get better error messages
      {-let synthAttempt = do
           (ty, _) <- synthExpr dbg def_env [] expr
           solved <- solveConstraints
           if solved
             then return ty
             else fail "No synth possible"
      synthTy <-    runMaybeT
                  . liftIO
                  . flip evalStateT (0, ground, CPoly)
                  . flip runReaderT nameMap
                  . unwrap . runMaybeT $ synthAttempt -}

      return ((var, ty, Nothing, env') : results, (var, ty) : def_env)

-- Make type error report
mkReport :: (Id, Type, Maybe Type, Maybe (Env TyOrDisc))
         -> String
mkReport (var, ty, synthTy, Nothing) =
    "'" ++ var ++ "' does not type check, signature was: " ++ pretty ty
        ++ (case synthTy of { Nothing -> ""; Just ty' -> "\n but infered: " ++ pretty ty' })
        ++ ".\n Try annotating the types of functions or fixing a signature."
mkReport _ = ""

-- Type check an expression

--  `checkExpr dbg defs gam t expr` computes `Just delta`
--  if the expression type checks to `t` in environment `gam`:
--  where `delta` gives the post-computation context for expr
--  (which explains the exact coeffect demands)
--  or `Nothing` if the typing does not match.

checkExpr :: Bool         -- turn on dbgging
          -> Env Type     -- environment of top-level definitions
          -> Env TyOrDisc -- local typing context
          -> Type         -- type
          -> Expr         -- expression
          -> MaybeT Checker (Env TyOrDisc)

checkExpr dbg defs gam (FunTy sig tau) (Val (Abs x e)) = do
  gam' <- extCtxt gam x (Left sig)
  checkExpr dbg defs gam' tau e

checkExpr _ _ _ tau (Val (Abs _ _)) =
    illTyped $ "Expected a function type, but got " ++ pretty tau

{-

[G] |- e : t
 ---------------------
[G]*r |- [e] : []_r t

-}

checkExpr dbg defs gam (Box demand tau) (Val (Promote e)) = do
    gamF        <- discToFreshVarsIn (fvs e) gam
    gam'        <- checkExpr dbg defs gamF tau e
    let gam'' = multAll (fvs e) demand gam'
    equalCtxts dbg gam gam''
    return gam''

checkExpr dbg defs gam tau (App e1 e2) = do
    (sig, gam1) <- synthExpr dbg defs gam e2
    gam2 <- checkExpr dbg defs gam (FunTy sig tau) e1
    gam1 `ctxPlus` gam2


checkExpr dbg defs gam tau e = do
  (tau', gam') <- synthExpr dbg defs gam e
  tyEq <- (equalTypes dbg) tau tau'
  equalCtxts dbg gam gam'
  if tyEq then return gam'
          else illTyped $ "Checking: (" ++ pretty e ++ "), "
                        ++ show tau ++ " != " ++ show tau'

-- Check whether two types are equal, and at the same time
-- generate coeffect equality constraints
equalTypes :: Bool -> Type -> Type -> MaybeT Checker Bool
equalTypes dbg (FunTy t1 t2) (FunTy t1' t2') = do
  eq1 <- equalTypes dbg t1 t1'
  eq2 <- equalTypes dbg t2 t2'
  return (eq1 && eq2)

equalTypes _ (ConT t) (ConT t') = do
  return (t == t')

equalTypes dbg (Diamond ef t) (Diamond ef' t') = do
  eq <- equalTypes dbg t t'
  if (ef == ef')
    then return eq
    else illTyped $ "Effect mismatch: " ++ pretty ef ++ "!=" ++ pretty ef'

equalTypes dbg (Box c t) (Box c' t') = do
  -- Debugging
  when dbg $ liftIO $ putStrLn (pretty c ++ " == " ++ pretty c')

  checkerState <- get
  let kind = coeffectKind checkerState
  let predicate' = do
        (pred, fVars) <- predicate checkerState
        return ((compile c fVars kind .== compile c' fVars kind) &&& pred, fVars)

  put $ checkerState { predicate = predicate' }
  eq <- equalTypes dbg t t'
  return eq

equalTypes _ t1 t2 = illTyped $ "Type " ++ pretty t1 ++ " != " ++ pretty t2

-- Synthesise types on expressions
synthExpr :: Bool
          -> Env Type
          -> Env TyOrDisc
          -> Expr
          -> MaybeT Checker (Type, Env TyOrDisc)

-- Variables
synthExpr _ _ _ (Val (Var "read")) = do
  return (Diamond ["R"] (ConT TyInt), [])

synthExpr _ _ _ (Val (Var "write")) = do
  return (FunTy (ConT TyInt) (Diamond ["W"] (ConT TyInt)), [])

synthExpr dbg defs gam (Val (Pure e)) = do
  (ty, gam') <- synthExpr dbg defs gam e
  return (Diamond [] ty, gam')

synthExpr dbg defs gam (Case e cases) = do
  (ty, gam') <- synthExpr dbg defs gam e
  branchTysAndCtxts <-
    forM cases $ \(pi, ei) ->
      case ctxtFromTypedPattern ty pi of
        Just gamLocal -> synthExpr dbg defs (gam' ++ gamLocal) ei
        Nothing       -> illTyped $ "Type of the guard expression " ++ pretty ei
                                ++ " does not match the type of the pattern "
                               ++ pretty pi
  let (branchTys, branchCtxts) = unzip branchTysAndCtxts
  eqTypes <- foldM (\a r -> equalTypes dbg a r >>=
                             (\b -> if b then return r else illTyped $ "Types of branches don't match in case")) (head branchTys) (tail branchTys)
  eqResultGam <- foldM (\a r -> joinCtxts dbg a r) empty branchCtxts
  return (eqTypes, eqResultGam)

synthExpr dbg defs gam (LetDiamond var ty e1 e2) = do
  gam'        <- extCtxt gam var (Left ty)
  (tau, gam1) <- synthExpr dbg defs gam' e2
  case tau of
    Diamond ef2 tau' -> do
       (sig, gam2) <- synthExpr dbg defs gam e1
       case sig of
         Diamond ef1 ty' | ty == ty' -> do
             gamNew <- gam1 `ctxPlus` gam2
             return (Diamond (ef1 ++ ef2) tau', gamNew)
         _ -> illTyped $ "Expected a diamond type"
    _ -> illTyped $ "Expected a diamond type"

synthExpr _ defs gam (Val (Var x)) = do
   nameMap <- ask
   case lookup x gam of
     Nothing ->
       case lookup x defs of
         Just ty  -> do
           ty' <- lift $ freshPolymorphicInstance ty
           return (ty', [])
         Nothing  -> illTyped $ "I don't know the type for "
                              ++ show (unrename nameMap x)
                              ++ " in environment " ++ pretty gam
                              ++ " or definitions " ++ pretty defs

     Just (Left ty)       -> return (ty, [(x, Left ty)])
     Just (Right (c, ty)) -> return (ty, [(x, Right (oneKind (kindOf c), ty))])

-- Constants (numbers)
synthExpr _ _ _ (Val (Num _)) = return (ConT TyInt, [])

-- Application
synthExpr dbg defs gam (App e e') = do
    (f, gam1) <- synthExpr dbg defs gam e
    case f of
      (FunTy sig tau) -> do
         gam2 <- checkExpr dbg defs gam sig e'
         gamNew <- gam1 `ctxPlus` gam2
         return (tau, gamNew)
      _ -> illTyped "Left-hand side of app is not a function type"

-- Promotion
synthExpr dbg defs gam (Val (Promote e)) = do
   gamF <- discToFreshVarsIn (fvs e) gam
   (t, gam') <- synthExpr dbg defs gamF e
   var <- lift . freshVar $ "prom_" ++ [head (pretty e)]
   return (Box (CVar var) t, (multAll (fvs e) (CVar var) gam'))

-- Letbox
synthExpr dbg defs gam (LetBox var t e1 e2) = do
   cvar <- lift $ freshVar ("binder_" ++ var)
   gam' <- extCtxt gam var (Right (CVar cvar, t))
   (tau, gam1) <- synthExpr dbg defs gam' e2
   case lookup var gam1 of
       Just (Right (demand, t')) | t == t' -> do
            when dbg $ liftIO . putStrLn $ "Demand for " ++ var ++ " = " ++ pretty demand
            gam2 <- checkExpr dbg defs gam (Box demand t) e1
            gamNew <- gam1 `ctxPlus` gam2
            return (tau, gamNew)
       _ -> do
         nm <- ask
         illTyped $ "Context of letbox does not have " ++ (unrename nm var)

-- BinOp
synthExpr dbg defs gam (Binop op e e') = do
    (t, gam1)  <- synthExpr dbg defs gam e
    (t', gam2) <- synthExpr dbg defs gam e'
    case (t, t') of
        (ConT TyInt, ConT TyInt) -> do
            gamNew <- gam1 `ctxPlus` gam2
            return (ConT TyInt, gamNew)
        _ ->
            illTyped "Binary op does not have two int expressions"

synthExpr _ _ _ e = illTyped $ "General synth fail " ++ pretty e


solveConstraints :: MaybeT Checker Bool
solveConstraints = do
  checkerState <- get
  let pred = do { (p, _) <- predicate checkerState; return p }
  thmRes <- liftIO . prove $ pred
  case thmRes of
     -- Tell the user if there was a hard proof error (e.g., if
     -- z3 is not installed/accessible).
     -- TODO: give more information
     ThmResult (ProofError _ msgs) -> illTyped $ "Prover error:" ++ unlines msgs
     _ -> if modelExists thmRes
           then
             case getModel thmRes of
               Right (False, ce :: [ Integer ] ) -> do
                   satRes <- liftIO . sat $ pred
                   let maybeModel = case ce of
                                     [] -> ""
                                     _ -> "Falsifying model: " ++ show ce ++ " - "
                   let satModel = case satRes of
                                    (SatResult (Unsatisfiable {})) -> ""
                                    _ -> "\nSAT result: \n" ++ show satRes
                   illTyped $ show thmRes ++ maybeModel ++ satModel

               Right (True, _) -> illTyped $ "Returned probable model."
               Left str        -> illTyped $ "Solver fail: " ++ str
           else return True

-- Generate a fresh alphanumeric variable name
freshVar :: String -> Checker String
freshVar s = Checker $ do
  checkerState <- get
  let v = uniqueVarId checkerState
  let prefix = s ++ "_" ++ ["a", "b", "c", "d"] !! (v `mod` 4)
  let cvar = prefix ++ show v
  let predicate' = do
      (pred, vars) <- predicate checkerState
      solverVar    <- exists cvar
      return (pred &&& solverVar .>= (literal 0), (cvar, solverVar) : vars)
  put $ checkerState { uniqueVarId = v + 1, predicate = predicate' }
  return cvar

-- Generate a fresh alphanumeric variable name
freshUniversalVar :: String -> Checker ()
freshUniversalVar cvar = Checker $ do
  checkerState <- get
  let predicate' = do
      (pred, vars) <- predicate checkerState
      case lookup cvar vars of
        Nothing -> do solverVar    <- exists cvar
                      return (pred &&& solverVar .>= (literal 0), (cvar, solverVar) : vars)
        _ -> return (pred, vars)
  put $ checkerState { predicate = predicate' }
  return ()


-- Wrappers to make it clear the provneance of arguments
-- to equality, since equality is not actually symmetric
-- due to allowing over-approximating in the checker
-- output.

newtype CheckerInput a = CheckerInput a
newtype CheckerOutput a = CheckerOutput a

equalCtxts :: Bool -> Env TyOrDisc -> Env TyOrDisc -> MaybeT Checker ()
equalCtxts dbg env1 env2 =
  let env  = env1 `keyIntersect` env2
      env' = env2 `keyIntersect` env1
  in
    if length env == length env'
    && map fst env == map fst env'
      then do
        checkerState <- get
        let kind = coeffectKind checkerState
        let predicate' = do
              (pred, vars) <- predicate checkerState
              eqs <- return . foldr (&&&) true $ zipWith (makeEquality dbg kind vars) env env'
              return (eqs &&& pred, vars)
        put $ checkerState { predicate = predicate' }
      else illTyped $ "Environments do not match in size or types: "
            ++ show env ++ " - " ++ show env'

makeEquality :: Bool
             -> CKind
             -> SolverVars
             -> (Id, TyOrDisc)
             -> (Id, TyOrDisc)
             -> SBool
makeEquality _ _ _ (_, Left _) (_, Left _) = true
makeEquality dbg k freeVars (_, Right (c1, _)) (_, Right (c2, _)) =
   (if dbg then ((pretty c1) ++ " == " ++ (pretty c2)) `trace` () else ()) `seq`
   compile c1 freeVars k .== compile c2 freeVars k
makeEquality _ _ _ _ _ = true

joinCtxts :: Bool -> Env TyOrDisc -> Env TyOrDisc -> MaybeT Checker (Env TyOrDisc)
joinCtxts dbg env1 env2 =
  let env  = env1 `keyIntersect` env2
      env' = env2 `keyIntersect` env1
  in
    if length env == length env'
    && map fst env == map fst env'
      then do
        error "Least-upper bound of contexts not implemented yet"
        {-
        checkerState <- get
        let kind = coeffectKind checkerState
        let predicate' = do
              (pred, vars) <- predicate checkerState
              eqs <- return . foldr (&&&) true $ zipWith (makeEquality dbg kind vars) env env'
              return (eqs &&& pred, vars)
        put $ checkerState { predicate = predicate' } -}
      else illTyped $ "Environments do not match in size or types: "
            ++ show env ++ " - " ++ show env'


addAnyUniversalsTy :: Type -> Checker ()
addAnyUniversalsTy (FunTy t1 t2) = do
  addAnyUniversalsTy t1
  addAnyUniversalsTy t2
addAnyUniversalsTy (Box c t) = do
  addAnyUniversals c
  addAnyUniversalsTy t
addAnyUniversalsTy _ = return ()

addAnyUniversals :: Coeffect -> Checker ()
addAnyUniversals (CVar v) = do
  freshUniversalVar v
  return ()
addAnyUniversals (CPlus c d) = do
 addAnyUniversals c
 addAnyUniversals d
addAnyUniversals (CTimes c d) = do
 addAnyUniversals c
 addAnyUniversals d
addAnyUniversals _ = return ()

illTyped :: String -> MaybeT Checker a
illTyped s = liftIO (putStrLn $ "Type error: " ++ s) >> MaybeT (return Nothing)

freshPolymorphicInstance :: Type -> Checker Type
freshPolymorphicInstance (FunTy t1 t2) = do
  t1' <- freshPolymorphicInstance t1
  t2' <- freshPolymorphicInstance t2
  return $ FunTy t1' t2'
freshPolymorphicInstance (Box c t) = do
  t' <- freshPolymorphicInstance t
  c' <- freshPolyCoeffect c
  return $ Box c' t'
freshPolymorphicInstance t = return t

freshPolyCoeffect :: Coeffect -> Checker Coeffect
freshPolyCoeffect (CVar cvar) = do
  checkerState <- get
  let v = uniqueVarId checkerState
  let cvar' = cvar ++ show v
  put $ checkerState { uniqueVarId = v + 1 }
  freshUniversalVar cvar'
  return $ CVar cvar'

freshPolyCoeffect (CPlus c1 c2) = do
  c1' <- freshPolyCoeffect c1
  c2' <- freshPolyCoeffect c2
  return $ CPlus c1' c2'
freshPolyCoeffect (CTimes c1 c2) = do
  c1' <- freshPolyCoeffect c1
  c2' <- freshPolyCoeffect c2
  return $ CTimes c1' c2'
freshPolyCoeffect c = return c

compile :: Coeffect -> SolverVars -> CKind -> SInteger
compile (Level n) _ _ = (fromInteger . toInteger $ n) :: SInteger
compile (Nat n) _ _ = (fromInteger . toInteger $ n) :: SInteger
compile (CVar v) vars _ =
  case lookup v vars of
   Just cvar -> cvar
   Nothing   -> error $ "Looking up a variable '" ++ v ++ "' in " ++ show vars

compile (CPlus n m) vars CLevel =
    compile n vars CLevel `smax` compile m vars CLevel

compile (CPlus n m) vars k =
    compile n vars k + compile m vars k

compile (CTimes n m) vars CLevel =
    compile n vars CLevel `smin` compile m vars CLevel

compile (CTimes n m) vars k =
    compile n vars k * compile m vars k

relevantSubEnv :: [Id] -> [(Id, t)] -> [(Id, t)]
relevantSubEnv vars env = filter relevant env
 where relevant (var, _) = var `elem` vars

-- Replace all top-level discharged coeffects
discToFreshVarsIn :: [Id] -> Env TyOrDisc -> MaybeT Checker (Env TyOrDisc)
discToFreshVarsIn vars env = MaybeT $ mapM toFreshVar (relevantSubEnv vars env)
                                      >>= (return . Just)
  where
    toFreshVar (var, Right (_, t)) = do
      v <- freshVar var
      return $ (var, Right (CVar v, t))
    toFreshVar (var, Left t) = do
      v <- freshVar var
      return (var, Right (CVar v, t))

-- Combine two contexts
ctxPlus :: Env TyOrDisc -> Env TyOrDisc -> MaybeT Checker (Env TyOrDisc)
ctxPlus [] env2 = return env2
ctxPlus ((i, v) : env1) env2 = do
  env' <- extCtxt env2 i v
  ctxPlus env1 env'

-- ExtCtxt the environment
extCtxt :: Env TyOrDisc -> Id -> TyOrDisc -> MaybeT Checker (Env TyOrDisc)
extCtxt env var (Left t) = do
  nameMap <- ask
  var'     <- return $ unrename nameMap var
  case (lookup var env) of
    Just (Left t') ->
       if t == t'
        then illTyped $ "'" ++ var' ++ "' used more than once\n"
        else illTyped $ "Type clash for variable " ++ var'
    Just (Right (c, t')) ->
       if t == t'
         then return $ replace env var (Right (c `plus` (oneKind (kindOf c)), t))
         else illTyped $ "Type clash for variable " ++ var'
    Nothing -> return $ (var, Left t) : env

extCtxt env var (Right (c, t)) = do
  nameMap <- ask
  case (lookup var env) of
    Just (Right (c', t')) ->
        if t == t'
        then return $ replace env var (Right (c `plus` c', t'))
        else do
          var' <- return $ unrename nameMap var
          illTyped $ "Type clash for variable " ++ var'
    Just (Left t') ->
        if t == t'
        then return $ replace env var (Right (c `plus` (oneKind (kindOf c)), t))
        else do
          var' <- return $ unrename nameMap var
          illTyped $ "Type clash for variable " ++ var'
    Nothing -> return $ (var, Right (c, t)) : env
