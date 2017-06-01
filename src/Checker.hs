{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Checker where

import Expr
import Eval hiding (Env, empty, extend)
import Type

import Data.List
import Data.Maybe
import Data.Either
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Control.Monad
import Data.SBV
import Debug.Trace

-- For fresh name generation
type VarCounter  = Int

-- Map from Ids to symbolic integer variables in the solver
type SolverVars  = [(Id, SInteger)]

-- Pair of a predicate and the solver variables
type SolverInfo  = Symbolic (SBool, SolverVars)

-- State of the check/synth functions
data TypeState a = TS { unwrap ::
    StateT (VarCounter, SolverInfo) IO a
  }

-- Checking (top-level)
check :: [Def] -> Bool -> IO (Either String Bool)
check defs dbg = do
    (results, _) <- flip evalStateT (0, ground) (unwrap $ foldM checkDef ([], empty) defs)
    if (and . map (\(_, _, check) -> isJust check) $ results)
      then return . Right $ True
      else return . Left  $ intercalate "\n" (map mkReport results)
  where
    ground = return (true, [])

    checkDef (results, def_env) (Def var expr ty) = do
      addAnyUniversalsTy ty
      env' <- runMaybeT $ do
               env' <- checkExpr dbg def_env [] ty expr
               solved <- solveConstraints
               if solved
                 then return ()
                 else illTyped "Constraints violated"
               return env'
      return ((var, ty, env') : results, (var, ty) : def_env)

-- Make type error report
mkReport :: (Id, Type, Maybe (Env TyOrDisc))
         -> String
mkReport (var, ty, Nothing) =
    "'" ++ var ++ "' does not type check, expected: " ++ pretty ty
        ++ ".\n Try annotating the types of functions or fixing a signature."
mkReport _ = ""

-- Checking on expressions
checkExpr :: Bool         -- turn on dbgging
          -> Env Type     -- environment of top-level definitions
          -> Env TyOrDisc -- local typing context
          -> Type         -- type
          -> Expr         -- expression
          -> MaybeT TypeState (Env TyOrDisc)

checkExpr dbg defs gam (FunTy sig tau) (Abs x e) =
  checkExpr dbg defs (extCtxt gam x (Left sig)) tau e

{-

[G] |- e : t
---------------------
[G]*r |- [e] : []_r t

-}

checkExpr dbg defs gam (Box demand tau) (Promote e) = do
    gamF        <- discToFreshVarsIn (fvs e) gam
    gam'        <- checkExpr dbg defs gamF tau e
    equalCtxts dbg gam (multAll (fvs e) demand gam')
    return gam

checkExpr dbg defs gam tau (App e1 e2) = do
    (sig, gam1) <- synthExpr dbg defs gam e2
    gam2 <- checkExpr dbg defs gam1 (FunTy sig tau) e1
    return gam

checkExpr dbg defs gam tau (Abs x e) =
    illTyped "Checking abs"

checkExpr dbg defs gam tau e = do
  (tau', gam') <- synthExpr dbg defs gam e
  tyEq <- (typesEq dbg) tau tau'
  equalCtxts dbg gam gam'
  if tyEq then return gam
          else illTyped $ "Checking: (" ++ pretty e ++ "), "
                        ++ show tau ++ " != " ++ show tau'

-- Check whether two types are equal, and at the same time
-- generate coeffec equality constraints
typesEq :: Bool -> Type -> Type -> MaybeT TypeState Bool
typesEq dbg (FunTy t1 t2) (FunTy t1' t2') = do
  eq1 <- typesEq dbg t1 t1'
  eq2 <- typesEq dbg t2 t2'
  return (eq1 && eq2)

typesEq _ (ConT t) (ConT t') = do
  return (t == t')

typesEq dbg (Diamond ef t) (Diamond ef' t') = do
  eq <- typesEq dbg t t'
  if (ef == ef')
    then return eq
    else illTyped $ "Effect mismatch: {" ++ intercalate "," ef
                     ++ "} != {" ++ intercalate "," ef' ++ "}"

typesEq dbg (Box c t) (Box c' t') = do
  -- Dbgging
  when dbg $ liftio $ putStrLn (pretty c ++ " == " ++ pretty c')

  (fvCount, symbolic) <- get
  let symbolic' = do
        (pred, fVars) <- symbolic
        return ((compile c fVars .== compile c' fVars) &&& pred, fVars)

  put (fvCount, symbolic')
  eq <- typesEq dbg t t'
  return eq

typesEq _ t1 t2 = illTyped $ "Type " ++ pretty t1 ++ " != " ++ pretty t2

-- Synthesise types on expressions
synthExpr :: Bool
          -> Env Type
          -> Env TyOrDisc
          -> Expr
          -> MaybeT TypeState (Type, Env TyOrDisc)

-- Variables
synthExpr dbg defs gam (Var "read") = do
  return (Diamond ["R"] (ConT TyInt), gam)

synthExpr dbg defs gam (Var "write") = do
  return (FunTy (ConT TyInt) (Diamond ["W"] (ConT TyInt)), gam)

synthExpr dbg defs gam (Pure e) = do
  (ty, gam') <- synthExpr dbg defs gam e
  return (Diamond [] ty, gam')

synthExpr dbg defs gam (LetDiamond id ty e1 e2) = do
  (tau, gam1) <- synthExpr dbg defs (extCtxt gam id (Left ty)) e2
  case tau of
    Diamond ef2 tau' -> do
       (sig, gam2) <- synthExpr dbg defs gam1 e1
       case sig of
         Diamond ef1 ty' | ty == ty' -> return (Diamond (ef1 ++ ef2) ty', gam2)
         _ -> illTyped $ "Expected a diamond type"
    _ -> illTyped $ "Expected a diamond type"

synthExpr dbg defs gam (Var x) = do
   case lookup x gam of
     Nothing ->
       case lookup x defs of
         Just ty  -> do
           ty' <- liftTS $ freshPolymorphicInstance ty
           return (ty', gam)
         Nothing  -> illTyped $ "I don't know the type for " ++ show x

     Just (Left ty)       -> return (ty, gam)
     Just (Right (c, ty)) -> return (ty, replace gam x (Right (one, ty)))

-- Constants (numbers)
synthExpr dbg defs gam (Num _) = return (ConT TyInt, gam)

-- Application
synthExpr dbg defs gam (App e e') = do
    (f, gam1) <- synthExpr dbg defs gam e
    case f of
      (FunTy sig tau) -> do
         checkExpr dbg defs gam sig e'
         return (tau, gam1)
      _ -> illTyped "Left-hand side of app is not a function type"

-- Promotion
synthExpr dbg defs gam (Promote e) = do
   gamF <- discToFreshVarsIn (fvs e) gam
   (t, gam') <- synthExpr dbg defs gamF e
   var <- liftTS . freshVar $ "prom_" ++ [head (pretty e)]
   return (Box (CVar var) t, (multAll (fvs e) (CVar var) gam'))

-- Letbox
synthExpr dbg defs gam (LetBox var t e1 e2) = do
   cvar <- liftTS $ freshVar ("binder_" ++ var)
   (tau, gam1) <- synthExpr dbg defs (extCtxt gam var (Right (CVar cvar, t))) e2
   case lookup var gam1 of
       Just (Right (demand, t')) | t == t' -> do
            when dbg $ liftio . putStrLn $ "Demand for " ++ var ++ " = " ++ pretty demand
            checkExpr dbg defs gam (Box demand t) e1
            return (tau, gam1)
       _ -> illTyped $ "Context of letbox does not have " ++ var

-- BinOp
synthExpr dbg defs gam (Binop op e e') = do
    (t, gam1)  <- synthExpr dbg defs (relevantSubEnv (fvs e) gam) e
    (t', gam2) <- synthExpr dbg defs (relevantSubEnv (fvs e') gam) e'
    case (t, t') of
        (ConT TyInt, ConT TyInt) -> return (ConT TyInt, gam1 `ctxPlus` gam2)
        _                        -> illTyped "Binary op does not have two int expressions"

synthExpr _ defs gam e = illTyped $ "General synth fail " ++ show e


solveConstraints :: MaybeT TypeState Bool
solveConstraints = do
  (_, symbolic) <- get
  let predicate = do { (pred, vars) <- symbolic; return pred }
  thmRes <- liftio . prove $ predicate
  case thmRes of
     -- Tell the user if there was a hard proof error (e.g., if
     -- z3 is not installed/accessible).
     -- TODO: give more information
     ThmResult (ProofError _ msgs) -> illTyped $ "Prover error:" ++ unlines msgs
     _ -> if modelExists thmRes
           then
             case getModel thmRes of
               Right (False, ce :: [ Integer ] ) -> do
                   satRes <- liftio . sat $ predicate
                   illTyped $ "Returned model " ++ show ce ++ " - " ++ show thmRes
                            ++ "\nSAT result: \n" ++ show satRes
               Right (True, _) -> illTyped $ "Returned probable model."
               Left str        -> illTyped $ "Solver fail: " ++ str
           else return True

-- Generate a fresh alphanumeric variable name
freshVar :: String -> TypeState String
freshVar s = TS $ do
  (v, symbolic) <- get
  let prefix = s ++ "_" ++ ["a", "b", "c", "d"] !! (v `mod` 4)
  let cvar = prefix ++ show v
  let symbolic' = do
      (pred, vars) <- symbolic
      solverVar    <- exists cvar
      return (pred &&& solverVar .>= (literal 0), (cvar, solverVar) : vars)
  put (v+1, symbolic')
  return cvar

-- Generate a fresh alphanumeric variable name
freshUniversalVar :: String -> TypeState String
freshUniversalVar cvar = TS $ do
  (v, symbolic) <- get
  let symbolic' = do
      (pred, vars) <- symbolic
      case lookup cvar vars of
        Nothing -> do solverVar    <- exists cvar
                      return (pred &&& solverVar .>= (literal 0), (cvar, solverVar) : vars)
        _ -> return (pred, vars)
  put (v, symbolic')
  return cvar

liftm :: Maybe a -> MaybeT TypeState a
liftm = MaybeT . return

equalCtxts :: Bool -> Env TyOrDisc -> Env TyOrDisc -> MaybeT TypeState ()
equalCtxts dbg env1 env2 =
  let env  = env1 `keyIntersect` env2
      env' = env2 `keyIntersect` env1
  in
    if length env == length env'
    && map fst env == map fst env'
      then do
        (fv, symbolic) <- get
        let symbolic' = do
              (pred, vars) <- symbolic
              eqs <- return . foldr (&&&) true $ zipWith (makeEqual dbg vars) env env'
              return (eqs &&& pred, vars)
        put (fv, symbolic')
      else illTyped $ "Environments do not match in size or types: " ++ show env ++ " - " ++ show env'

makeEqual dbg freeVars (_, Left _) (_, Left _) = true
makeEqual dbg freeVars (_, Right (c1, _)) (_, Right (c2, _)) =
   (if dbg then ((pretty c1) ++ " == " ++ (pretty c2)) `trace` () else ()) `seq`
   compile c1 freeVars .== compile c2 freeVars
makeEqual _ _ _ _ = true


addAnyUniversalsTy (FunTy t1 t2) = do
  addAnyUniversalsTy t1
  addAnyUniversalsTy t2
addAnyUniversalsTy (Box c t) = do
  addAnyUniversals c
  addAnyUniversalsTy t
addAnyUniversalsTy _ = return ()

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

illTyped :: String -> MaybeT TypeState a
illTyped s = liftio (putStrLn s) >> MaybeT (return Nothing)

liftio :: forall a . IO a -> MaybeT TypeState a
liftio m = MaybeT (TS ((lift (m >>= (return . Just)))
                   :: StateT (VarCounter, SolverInfo) IO (Maybe a)))

instance Monad TypeState where
  return = TS . return
  (TS x) >>= f = TS (x >>= (unwrap . f))

instance Functor TypeState where
  fmap f (TS x) = TS (fmap f x)

instance Applicative TypeState where
  pure    = return
  f <*> x = f >>= \f' -> x >>= \x' -> return (f' x')

freshPolymorphicInstance (FunTy t1 t2) = do
  t1' <- freshPolymorphicInstance t1
  t2' <- freshPolymorphicInstance t2
  return $ FunTy t1' t2'
freshPolymorphicInstance (Box c t) = do
  t' <- freshPolymorphicInstance t
  c' <- freshPolyCoeffect c
  return $ Box c' t'
freshPolymorphicInstance t = return t

freshPolyCoeffect (CVar cvar) = do
  (v, s) <- get
  let cvar' = cvar ++ show v
  put (v+1, s)
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

liftTS :: TypeState a -> MaybeT TypeState a
liftTS t = MaybeT $ t >>= (return . Just)

instance MonadState (VarCounter, SolverInfo) TypeState where
  get = TS get
  put s = TS (put s)

compile :: Coeffect -> SolverVars -> SInteger
compile (Nat n) _ = (fromInteger . toInteger $ n) :: SInteger
compile (CVar v) vars =
  case lookup v vars of
   Just cvar -> cvar
   Nothing   -> error $ "Looking up a variable '" ++ v ++ "' in " ++ show vars
compile (CPlus n m) vars = compile n vars + compile m vars
compile (CTimes n m) vars = compile n vars * compile m vars


relevantSubEnv vars env = filter relevant env
 where relevant (id, _) = id `elem` vars

-- Replace all top-level discharged coeffects
discToFreshVarsIn :: [Id] -> Env TyOrDisc -> MaybeT TypeState (Env TyOrDisc)
discToFreshVarsIn vars env = MaybeT $ mapM toFreshVar (relevantSubEnv vars env)
                                      >>= (return . Just)
  where
    toFreshVar (id, Right (c, t)) = do
      v <- freshVar id
      return $ (id, Right (CVar v, t))
    toFreshVar (id, Left t) = do
      v <- freshVar id
      return (id, Right (CVar v, t))