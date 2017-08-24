{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Checker.Checker where

import Syntax.Expr
import Syntax.Pretty
import Checker.Types
import Checker.Coeffects
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
    -- Build the computation to check all the defs (in order)...
    let checkedDefs = foldM checkDef ([], empty) defs
    -- ... and evaluate the computation with initial state
    (results, _) <- evalChecker initState nameMap checkedDefs

    -- If all definitions type checkerd, then the whole file type checkers
    if (and . map (\(_, _, _, checked) -> isJust checked) $ results)
      then return . Right $ True
      -- Otherwise, show the checking reports
      else return . Left  $ intercalate "\n" (map mkReport results)
  where
    checkDef (results, def_env) (Def var expr _ tys@(Forall ckinds ty)) = do
      mapM freshSolverCoeffectVar ckinds
      env' <- runMaybeT $ do
               env' <- checkExprTS dbg def_env [] tys expr
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

      return ((var, tys, Nothing, env') : results, (var, tys) : def_env)

-- Make type error report
mkReport :: (Id, TypeScheme, Maybe TypeScheme, Maybe (Env TyOrDisc))
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

checkExprTS :: Bool          -- turn on debgging
          -> Env TypeScheme  -- environment of top-level definitions
          -> Env TyOrDisc    -- local typing context
          -> TypeScheme      -- typeScheme
          -> Expr            -- expression
          -> MaybeT Checker (Env TyOrDisc)

checkExprTS dbg defs gam (Forall ckinds ty) e = do
  -- Coeffect kinds only need a local resolution; set kind environment to scheme
  state <- get
  put (state { ckenv = ckinds, ckkenv = [("BleH", CPoly "")] })
  -- check expression against type
  checkExpr dbg defs gam ty e

checkExpr :: Bool             -- turn on debgging
          -> Env TypeScheme   -- environment of top-level definitions
          -> Env TyOrDisc     -- local typing context
          -> Type             -- type
          -> Expr             -- expression
          -> MaybeT Checker (Env TyOrDisc)

-- Checking of constants

checkExpr _ _ _ (ConT "Int") (Val (NumInt i)) = return []
  -- Automatically upcast integers to reals
checkExpr _ _ _ (ConT "Real") (Val (NumInt i)) = return []
checkExpr _ _ _ (ConT "Real") (Val (NumReal i)) = return []

checkExpr dbg defs gam (FunTy sig tau) (Val (Abs x e)) = do
  gamE <- extCtxt gam x (Left sig)
  gam' <- checkExpr dbg defs gamE tau e
  -- Linearity check, variables must be used exactly once
  case lookup x gam' of
    Nothing -> do
      nameMap <- ask
      illTyped $ unusedVariable (unrename nameMap x)
    Just _  -> return (eraseVar gam' x)

checkExpr _ _ _ tau (Val (Abs _ _)) =
    illTyped $ "Expected a function type, but got " ++ pretty tau

{-

[G] |- e : t
 ---------------------
[G]*r |- [e] : []_r t

-}

-- Promotion
checkExpr dbg defs gam (Box demand tau) (Val (Promote e)) = do
    state       <- get
    gamF        <- discToFreshVarsIn (fvs e) gam
    gam'        <- checkExpr dbg defs gamF tau e
    let gam'' = multAll (fvs e) demand gam'
    equalCtxts dbg gam gam''
    return gam''

-- Application
checkExpr dbg defs gam tau (App e1 e2) = do
    (sig, gam1) <- synthExpr dbg defs gam e2
    gam2 <- checkExpr dbg defs gam (FunTy sig tau) e1
    gam1 `ctxPlus` gam2

-- all other rules, go to synthesis
checkExpr dbg defs gam tau e = do
  (tau', gam') <- synthExpr dbg defs gam e
  tyEq <- equalTypes dbg tau tau'
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

equalTypes dbg ty@(Box c t) ty'@(Box c' t') = do
  -- Debugging
  when dbg $ liftIO $ putStrLn (pretty c ++ " == " ++ pretty c')
  kind <- mguCoeffectKinds c c'
  checkerState <- get
  let predicate' = do
        (pred, fVars) <- predicate checkerState
        let pred' = eqConstraint (compile c kind fVars) (compile c' kind fVars)
        return (pred &&& pred', fVars)
  put $ checkerState { predicate = predicate' }
  equalTypes dbg t t'

equalTypes _ t1 t2 = illTyped $ "Type " ++ pretty t1 ++ " != " ++ pretty t2

-- Synthesise types on expressions
synthExpr :: Bool
          -> Env TypeScheme
          -> Env TyOrDisc
          -> Expr
          -> MaybeT Checker (Type, Env TyOrDisc)

-- Constants (built-in effect primitives)
synthExpr _ _ _ (Val (Var "read")) = do
  return (Diamond ["R"] (ConT "Int"), [])

synthExpr _ _ _ (Val (Var "write")) = do
  return (FunTy (ConT "Int") (Diamond ["W"] (ConT "Int")), [])

-- Constants (booleans)
synthExpr _ _ _ (Val (Constr s)) | s == "False" || s == "True" =
  return (ConT "Bool", [])

-- Constants (numbers)
synthExpr _ _ _ (Val (NumInt i))  = return (ConT "Int", [])
synthExpr _ _ _ (Val (NumReal i)) = return (ConT "Real", [])

-- Variables
synthExpr dbg defs gam (Val (Pure e)) = do
  (ty, gam') <- synthExpr dbg defs gam e
  return (Diamond [] ty, gam')

synthExpr dbg defs gam (Case e cases) = do
  (ty, gam') <- synthExpr dbg defs gam e
  branchTysAndCtxts <-
    forM cases $ \(pi, ei) ->
      case ctxtFromTypedPattern ty pi of
        Just gamLocal -> synthExpr dbg defs (gam ++ gamLocal) ei
        Nothing       -> illTyped $ "Type of the guard expression " ++ pretty ei
                                ++ " does not match the type of the pattern "
                                ++ pretty pi
  let (branchTys, branchCtxts) = unzip branchTysAndCtxts
  eqTypes <- foldM (\a r -> do
                     eq <- equalTypes dbg a r
                     if eq then return r
                           else illTyped $ "Types of branches don't match in case")
                   (head branchTys) (tail branchTys)
  eqResultGam <- foldM (\a r -> joinCtxts dbg a r) empty branchCtxts
  gamNew <- eqResultGam `ctxPlus` gam'
  return (eqTypes, gamNew)

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
         Just tyScheme  -> do
           ty' <- freshPolymorphicInstance tyScheme
           return (ty', [])
         Nothing  -> illTyped $ "I don't know the type for "
                              ++ show (unrename nameMap x)
                              ++ " in environment " ++ pretty gam
                              ++ " or definitions " ++ pretty defs

     Just (Left ty)       -> return (ty, [(x, Left ty)])
     Just (Right (c, ty)) -> return (ty, [(x, Right (one, ty))])

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
synthExpr dbg defs gam (LetBox var t k e1 e2) = do

    cvar <- lift $ freshVar ("binder_" ++ var)
    lift $ freshSolverCoeffectVar (cvar, k)
    gam' <- extCtxt gam var (Right (CVar cvar, t))

    (tau, gam2) <- synthExpr dbg defs gam' e2
    (demand, t) <-
      case lookup var gam2 of
        Just (Right (demand, t')) -> do
             eqT <- equalTypes dbg t t'
             if eqT then do
                when dbg $ liftIO . putStrLn $
                     "Demand for " ++ var ++ " = " ++ pretty demand
                return (demand, t)
              else do
                nameMap <- ask
                illTyped $ "An explicit signature is given "
                         ++ unrename nameMap var
                         ++ " : " ++ pretty t
                         ++ " but the actual type was " ++ pretty t'
        _ -> do
          -- If there is no explicit demand for the variable
          -- then this means it is not used
          -- Therefore c ~ 0
          checkerState <- get
          let predicate' = do
              (pred, fVars)   <- predicate checkerState
              let coeffectVar  = compile (CVar cvar) k fVars
              let coeffectZero = compile zero k fVars
              return ((coeffectVar `eqConstraint` coeffectZero) &&& pred, fVars)
          put $ checkerState { predicate = predicate' }
          return (zero, t)
    gam1 <- checkExpr dbg defs gam (Box demand t) e1
    gamNew <- gam1 `ctxPlus` gam2
    return (tau, gamNew)


-- BinOp
synthExpr dbg defs gam (Binop op e e') = do
    (t, gam1)  <- synthExpr dbg defs gam e
    (t', gam2) <- synthExpr dbg defs gam e'
    case (t, t') of
        (ConT n, ConT m) | isNum n && isNum m -> do
            gamNew <- gam1 `ctxPlus` gam2
            return (ConT $ joinNum n m, gamNew)
        _ ->
            illTyped "Binary op does not have two int expressions"
  where isNum "Int" = True
        isNum "Real" = True
        isNum _      = False
        joinNum "Int" "Int" = "Int"
        joinNum x "Real" = x
        joinNum "Real" x = x

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
  put $ checkerState { uniqueVarId = v + 1 }
  return cvar

-- Generate a fresh coeffect variable in the solver environment
freshSolverCoeffectVar :: (Id, CKind) -> Checker ()
freshSolverCoeffectVar (cvar, kind) = Checker $ do
  checkerState <- get
  let predicate' = do
      (pred, vars) <- predicate checkerState
      case lookup cvar vars of
        Nothing -> do (refinement, solverVar) <- freshCVar cvar kind
                      return (pred &&& refinement, (cvar, solverVar) : vars)
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
equalCtxts dbg env1 env2 = do
    let env  = env1 `keyIntersect` env2
        env' = env2 `keyIntersect` env1
    -- Postcondition: env and env' have the same length, same keys, same order
    checkerState <- get
    envUnif <- zipWithM unifyContextKinds env env'
    let predicate' = do
          (pred, vars) <- predicate checkerState
          let eqs = map (makeEquality dbg vars) envUnif
          return (foldr (&&&) pred eqs, vars)
    put $ checkerState { predicate = predicate' }

unifyContextKinds :: (Id, TyOrDisc) -> (Id, TyOrDisc) -> MaybeT Checker ((Id, TyOrDisc), (Id, TyOrDisc), Maybe CKind)
unifyContextKinds x@(_, Left _) y@(_, Left _) = return (x, y, Nothing)
unifyContextKinds x@(_, Right (c1, _)) y@(_, Right (c2, _)) = do
  kind <- mguCoeffectKinds c1 c2
  return (x, y, Just kind)

makeEquality :: Bool
             -> SolverVars
             -> ((Id, TyOrDisc), (Id, TyOrDisc), Maybe CKind)
             -> SBool
makeEquality _ _ ((_, Left _), (_, Left _), _) = true
makeEquality dbg freeVars ((_, Right (c1, _)), (_, Right (c2, _)), Just kind) =
  -- Debugging message
  (if dbg then ((pretty c1) ++ " == " ++ (pretty c2)) `trace` () else ()) `seq`
  eqConstraint (compile c1 kind freeVars) (compile c2 kind freeVars)

makeEquality _ _ _ = false

joinCtxts :: Bool -> Env TyOrDisc -> Env TyOrDisc -> MaybeT Checker (Env TyOrDisc)
joinCtxts dbg env1 env2 = do
    let env  = env1 `keyIntersect` env2
        env' = env2 `keyIntersect` env1
    -- Postcondition: env and env' have the same length, same keys, same order
    varEnv <- discToFreshVarsIn (map fst env) env

    checkerState <- get
    envUnif <- zipWithM unifyContextKinds env varEnv
    envUnif' <- zipWithM unifyContextKinds env' varEnv

    let predicate' = do
        (pred, vars) <- predicate checkerState
        let eqs1 = map (isUpperBound dbg vars) envUnif
        let eqs2 = map (isUpperBound dbg vars) envUnif'
        return (foldr (&&&) pred (eqs1 ++ eqs2), vars)
    put $ checkerState { predicate = predicate' }
    return $ varEnv ++ (env1 \\ env) ++ (env2 \\ env')

isUpperBound :: Bool
             -> SolverVars
             -- precondition: first component is a dischared variable coeffect
             -> ((Id, TyOrDisc), (Id, TyOrDisc), Maybe CKind)
             -> SBool
isUpperBound dbg vars ((id, Right (c1@(CVar var), t1)), (_, Right (c, t2)), Just ckind) =
    case lookup var vars of
        Just upperVar -> lteConstraint (compile c ckind vars) upperVar
        Nothing       -> error $ "Gram bug on " ++ show var
-- Ignore anything else
isUpperBound _ _ _ = true

freshPolymorphicInstance :: TypeScheme -> MaybeT Checker Type
freshPolymorphicInstance (Forall ckinds ty) = do
    renameMap <- mapM (lift . freshCoeffectVar) ckinds
    rename renameMap ty

  where
    rename renameMap (FunTy t1 t2) = do
      t1' <- rename renameMap t1
      t2' <- rename renameMap t2
      return $ FunTy t1' t2'
    rename renameMap (Box c t) = do
      c' <- renameC renameMap c
      t' <- rename renameMap t
      return $ Box c' t'
    rename _ t = return t

    renameC rmap (CPlus c1 c2) = do
      c1' <- renameC rmap c1
      c2' <- renameC rmap c2
      return $ CPlus c1' c2'

    renameC rmap (CTimes c1 c2) = do
      c1' <- renameC rmap c1
      c2' <- renameC rmap c2
      return $ CTimes c1' c2'

    renameC rmap (CVar v) =
      case (lookup v rmap) of
        Just v' -> return $ CVar v
        Nothing -> illTyped $ "Coeffect variable " ++ v ++ " is unbound"

    renameC _ c = return c

    freshCoeffectVar (cvar, kind) = do
      checkerState <- get
      let v = uniqueVarId checkerState
      let cvar' = cvar ++ show v
      put $ checkerState { uniqueVarId = v + 1 }
      freshSolverCoeffectVar (cvar', kind)
      return $ (cvar, cvar')

relevantSubEnv :: [Id] -> [(Id, t)] -> [(Id, t)]
relevantSubEnv vars env = filter relevant env
 where relevant (var, _) = var `elem` vars

-- Replace all top-level discharged coeffects with a variable and derelict anything else
-- but add a var
discToFreshVarsIn :: [Id] -> Env TyOrDisc -> MaybeT Checker (Env TyOrDisc)
discToFreshVarsIn vars env = do
    mapM toFreshVar (relevantSubEnv vars env)
  where
    toFreshVar (var, Right (c, t)) = do
      -- Create a fresh variable
      cvar  <- lift $ freshVar var
      ckind <- kindOf c
      -- Create a matching fresh solver variable (of the right kind)
      lift $ freshSolverCoeffectVar (cvar, ckind)
      -- Update the coeffect kind environment
      modify (\s -> s { ckenv = (cvar, ckind) : ckenv s })
      -- Return the freshened var-type mapping
      return $ (var, Right (CVar cvar, t))

    toFreshVar (var, Left t) = do
{-      v <- freshVar var
      -- TODO: check this
      return (var, Right (CVar var, t)) -}
      return (var, Right (COne, t))

-- Combine two contexts
ctxPlus :: Env TyOrDisc -> Env TyOrDisc -> MaybeT Checker (Env TyOrDisc)
ctxPlus [] env2 = return env2
ctxPlus ((i, v) : env1) env2 = do
  env' <- extCtxt env2 i v
  ctxPlus env1 env'

-- Erase a variable from the environment
eraseVar :: Env TyOrDisc -> Id -> Env TyOrDisc
eraseVar [] _ = []
eraseVar ((id, t):env) id' | id == id' = env
                           | otherwise = (id, t) : eraseVar env id'

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
         then return $ replace env var (Right (c `plus` one, t))
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
        then return $ replace env var (Right (c `plus` one, t))
        else do
          var' <- return $ unrename nameMap var
          illTyped $ "Type clash for variable " ++ var'
    Nothing -> return $ (var, Right (c, t)) : env

{- Helpers for error messages -}

unusedVariable var = "Linear variable " ++ var ++ " was never used."