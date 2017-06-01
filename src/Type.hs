{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Type where

import Expr
import Eval hiding (Env, empty, extend)
import Data.List
import Data.Maybe
import Data.Either
import Debug.Trace
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Control.Monad
import Data.SBV

type TyOrDisc = Either Type (Coeffect, Type)

class Semiring c where
  plus  :: c -> c -> c
  mult  :: c -> c -> c
  one   :: c
  zero  :: c

instance Semiring Coeffect where
  plus (Nat n) (Nat m) = Nat (n + m)
  plus c d = CPlus c d
  mult (Nat n) (Nat m) = Nat (n * m)
  mult c d = CTimes c d
  one = Nat 1
  zero = Nat 0

empty = []
type Env t = [(Id, t)]

-- replace an item in an environment
replace :: Env a -> Id -> a -> Env a
replace [] id v
  = [(id, v)]
replace ((id', _):env) id v | id == id'
  = (id', v) : env
replace (x : env) id v
  = x : replace env id v

-- ExtCtxt the environment
extCtxt :: Env TyOrDisc -> Id -> TyOrDisc -> Env TyOrDisc
extCtxt env id (Left t) =
  case (lookup id env) of
    Just (Left t') ->
       if t == t'
        then replace env id (Left t)
        else error $ "Type clash for variable " ++ id
    Just (Right (c, t')) ->
       if t == t'
         then replace env id (Right (c `plus` one, t))
         else error $ "Type clash for variable " ++ id
    Nothing -> (id, Left t) : env
extCtxt env id (Right (c, t)) =
  case (lookup id env) of
    Just (Right (c', t')) ->
        if t == t'
        then replace env id (Right (c `plus` c', t'))
        else error $ "Type clash for variable " ++ id
    Just (Left t') ->
        if t == t'
        then replace env id (Right (c `plus` one, t))
        else error $ "Type clash for variable " ++ id
    Nothing -> (id, Right (c, t)) : env

-- Given an environment, derelict and discharge all variables which are not discharged
multAll :: [Id] -> Coeffect -> Env TyOrDisc -> Env TyOrDisc

multAll _ _ []
    = []

multAll vars c ((id, Left t) : env) | id `elem` vars
    = (id, Right (c, t)) : multAll vars c env

multAll vars c ((id, Right (c', t)) : env) | id `elem` vars
    = (id, Right (c `mult` c', t)) : multAll vars c env

multAll vars c ((id, Left t) : env) = multAll vars c env
multAll vars c ((id, Right (_, t)) : env) = multAll vars c env

{-
-- Given an environment, derelict and discharge all variables which are not discharged
derelictAndMultAll :: Coeffect -> Env TyOrDisc -> Env TyOrDisc
derelictAndMultAll _ [] = []
derelictAndMultAll c ((id, Left t) : env)
    = (id, Right (c, t)) : derelictAndMultAll c env
derelictAndMultAll c ((id, Right (c', t)) : env)
    = (id, Right (c `mult` c', t)) : derelictAndMultAll c env

derelictAll :: Env TyOrDisc -> Env TyOrDisc
derelictAll [] = []
derelictAll ((id, Left t) : env) = (id, Right (zero, t)) : derelictAll env
derelictAll (e : env) = e : derelictAll env
-}


ctxPlus :: Env TyOrDisc -> Env TyOrDisc -> Env TyOrDisc
ctxPlus [] env2 = env2
ctxPlus ((i, v) : env1) env2 =
  ctxPlus env1 (extCtxt env2 i v)

instance Pretty (Type, Env TyOrDisc) where
  pretty (t, env) = pretty t

-- ground = forAll_ $ \(x :: SInt64) -> (true :: SBool, [])
ground' = return (true, [])
falsity = forAll_ $ \(x :: SInt64) -> false :: SBool

-- Checking (top-level)
check :: [Def] -> IO (Either String Bool)
check defs = do
    (results, _) <- flip evalStateT (0, ground') (unwrap $ foldM checkDef ([], empty) defs)
    if (and . map (\(_, _, check) -> isJust check) $ results)
      then return . Right $ True
      else return . Left  $ intercalate "\n" (map mkReport results)
  where
    checkDef (results, def_env) (Def var expr ty) = do
      addAnyUniversalsTy ty
      env' <- runMaybeT $ do
               env' <- checkExpr def_env [] ty expr
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
checkExpr :: Env Type -> Env TyOrDisc -> Type -> Expr -> MaybeT TypeState (Env TyOrDisc)
checkExpr bgam gam (FunTy sig tau) (Abs x e) =
  checkExpr bgam (extCtxt gam x (Left sig)) tau e

{-

[G] |- e : t
---------------------
[G]*r |- [e] : []_r t

-}

checkExpr bgam gam (Box demand tau) (Promote e) = do
    gamF        <- discToFreshVarsIn (fvs e) gam
    gam'        <- checkExpr bgam gamF tau e
    gam `equalCtxts` (multAll (fvs e) demand gam')
    return gam

checkExpr bgam gam tau (App e1 e2) = do
    (sig, gam1) <- synthExpr bgam gam e2
    gam2 <- checkExpr bgam gam1 (FunTy sig tau) e1
    return gam

checkExpr bgam gam tau (Abs x e) =
    illTyped "Checking abs"

checkExpr bgam gam tau e = do
  (tau', gam') <- synthExpr bgam gam e
  tyEq <- tau `typesEq` tau'
  if tyEq then return $ gam'
          else illTyped $ "Checking: (" ++ pretty e ++ "), "
                        ++ show tau ++ " != " ++ show tau'

typesEq :: Type -> Type -> MaybeT TypeState Bool
typesEq (FunTy t1 t2) (FunTy t1' t2') = do
  eq1 <- typesEq t1 t1'
  eq2 <- typesEq t2 t2'
  return (eq1 && eq2)
typesEq (ConT t) (ConT t') = do
  return (t == t')
typesEq (Box c t) (Box c' t') = do
  (fvCount, symbolic) <- (pretty c ++ " = " ++ pretty c') `trace` get
  let symbolic' = do
        (pred, fVars) <- symbolic
        return ((compile c fVars .== compile c' fVars) &&& pred, fVars)
  put (fvCount, symbolic')
  eq <- typesEq t t'
  return eq
typesEq _ _ = return false

liftm :: Maybe a -> MaybeT TypeState a
liftm = MaybeT . return

-- Synthesise on expressions
synthExpr :: Env Type -> Env TyOrDisc -> Expr -> MaybeT TypeState (Type, Env TyOrDisc)

-- Variables
synthExpr bgam gam (Var x) = do
   case lookup x gam of
     Nothing ->
       case lookup x bgam of
         Just ty  -> return (ty, gam)
         Nothing  -> illTyped $ "I don't know the type for " ++ show x
     Just (Left ty)       -> return (ty, gam)
     Just (Right (c, ty)) -> return (ty, replace gam x (Right (one, ty)))

-- Constants (numbers)
synthExpr bgam gam (Num _) = return (ConT TyInt, gam)

-- Application
synthExpr bgam gam (App e e') = do
    (f, gam1) <- synthExpr bgam gam e
    case f of
      (FunTy sig tau) -> do
         checkExpr bgam gam sig e'
         return (tau, gam1)
      _ -> illTyped "Left-hand side of app is not a function type"

-- Promotion
synthExpr bgam gam (Promote e) = do
   gamF <- discToFreshVarsIn (fvs e) gam
   (t, gam') <- synthExpr bgam gamF e
   var <- liftTS . freshVar $ "prom_" ++ [head (pretty e)]
   return (Box (CVar var) t, (multAll (fvs e) (CVar var) gam'))

-- Letbox
synthExpr bgam gam (LetBox var t e1 e2) = do
   cvar <- liftTS $ freshVar ("binder_" ++ var)
   (tau, gam1) <- synthExpr bgam (extCtxt gam var (Right (CVar cvar, t))) e2
   case lookup var gam1 of
       Just (Right (demand, t')) | t == t' -> do
            gam2 <- --("demand for " ++ var ++ " = " ++ pretty demand) `trace`
                    checkExpr bgam gam (Box demand t) e1
            return (tau, gam1)
       _ -> illTyped $ "Context of letbox does not have " ++ var ++ " discharged"

-- BinOp
synthExpr bgam gam (Binop op e e') = do
    (t, gam1)  <- synthExpr bgam gam e
    (t', gam2) <- synthExpr bgam gam e'
    case (t, t') of
        (ConT TyInt, ConT TyInt) -> return (ConT TyInt, gam1 `ctxPlus` gam2)
        _                        -> illTyped "Binary op does not have two int expressions"

synthExpr bgam gam e = illTyped $ "General synth fail " ++ show e

keyIntersect :: Env a -> Env a -> Env a
keyIntersect a b = sortBy (\a b -> fst a `compare` fst b) $ filter (appearsIn a) b
  where appearsIn a (id, _) = isJust $ lookup id a

equalCtxts :: Env TyOrDisc -> Env TyOrDisc -> MaybeT TypeState ()
equalCtxts env1 env2 =
  let env  = env1 `keyIntersect` env2
      env' = env2 `keyIntersect` env1
  in
    if length env == length env'
    && map fst env == map fst env'
      then do
        (fv, symbolic) <- get
        let symbolic' = do
              (pred, vars) <- symbolic
              eqs <- return . foldr (&&&) true $ zipWith (makeEqual vars) env env'
              return (eqs &&& pred, vars)
        put (fv, symbolic')
      else illTyped $ "Environments do not match in size or types: " ++ show env ++ " - " ++ show env'

makeEqual freeVars (_, Left _) (_, Left _) = true
makeEqual freeVars (_, Right (c1, _)) (_, Right (c2, _)) = do
   (pretty c1) ++ " == " ++ (pretty c2)
  `trace`
    compile c1 freeVars .== compile c2 freeVars
makeEqual _ _ _ = true


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

extractVars (_, Left _) = []
extractVars (_, Right (c, _)) = vars c

vars :: Coeffect -> [String]
vars (CVar v) = [v]
vars (CPlus n m) = vars n ++ vars m
vars (CTimes n m) = vars n ++ vars m
vars _ = []

compile :: Coeffect -> SolverVars -> SInteger
compile (Nat n) _ = (fromInteger . toInteger $ n) :: SInteger
compile (CVar v) vars =
  case lookup v vars of
   Just cvar -> cvar
   Nothing   -> error $ "Looking up a variable '" ++ v ++ "' in " ++ show vars
compile (CPlus n m) vars = compile n vars + compile m vars
compile (CTimes n m) vars = compile n vars * compile m vars

illTyped :: String -> MaybeT TypeState a
illTyped s = liftio (putStrLn s) >> MaybeT (return Nothing)

type VarCounter  = Int
type SolverVars  = [(String, SInteger)]
type SolverInfo  = Symbolic (SBool, SolverVars)
data TypeState a = TS { unwrap ::
    StateT (VarCounter, SolverInfo) IO a
  }

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
        Nothing -> do solverVar    <- forall cvar
                      return (pred &&& solverVar .>= (literal 0), (cvar, solverVar) : vars)
        _ -> return (pred, vars)
  put (v, symbolic')
  return cvar

liftTS :: TypeState a -> MaybeT TypeState a
liftTS t = MaybeT $ t >>= (return . Just)

instance MonadState (VarCounter, SolverInfo) TypeState where
  get = TS get
  put s = TS (put s)

-- Replace all top-level discharged coeffects
discToFreshVars :: Env TyOrDisc -> MaybeT TypeState (Env TyOrDisc)
discToFreshVars env = MaybeT $ mapM toFreshVar env >>= (return . Just)
  where
    toFreshVar (id, Right (c, t)) = do
      v <- freshVar id
      return $ (id, Right (CVar v, t))
    toFreshVar (id, Left t) = return (id, Left t)

discToFreshVarsIn :: [Id] -> Env TyOrDisc -> MaybeT TypeState (Env TyOrDisc)
discToFreshVarsIn vars env = MaybeT $ mapM toFreshVar relevantSubEnv
                                      >>= (return . Just)
  where
    relevantSubEnv = filter relevant env
    relevant (id, _) = id `elem` vars

    toFreshVar (id, Right (c, t)) = do
      v <- freshVar id
      return $ (id, Right (CVar v, t))
    toFreshVar (id, Left t) = do
      v <- freshVar id
      return (id, Right (CVar v, t))

deleteVar :: Eq a => a -> [(a, b)] -> [(a, b)]
deleteVar x [] = []
deleteVar x ((y, b) : m) | x == y = deleteVar x m
                      | otherwise = (y, b) : deleteVar x m