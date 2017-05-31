{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Type where

import Expr
import Eval hiding (Env, empty, extend)
import Data.List
import Data.Maybe
import Data.Either
import Debug.Trace
import Control.Monad.State
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
extCtxt env id (Left t)  = (id, Left t) : env
extCtxt env id (Right (c, t)) =
  case (lookup id env) of
    Just (Right (c', t')) ->
        if t == t'
        then replace env id (Right (c `plus` c', t'))
        else error $ "Typeclash for discharged variable"
    Just (Left _) -> error $ "Typeclash for discharged variable"
    Nothing -> (id, Right (c, t)) : env

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
    (results, _) <- foldM checkDef ([], empty) defs
    if (and . map (\(_, _, check) -> isJust check) $ results)
      then return . Right $ True
      else return . Left  $ intercalate "\n" (map mkReport results)
  where
    checkDef (results, env) (Def var expr ty) = do
      env' <- flip evalStateT (0, ground') . unwrap . runMaybeT
                                 $ do
                                     env' <- checkExpr env ty expr
                                     solved <- solveConstraints
                                     if solved
                                        then return ()
                                        else illTyped "Constraints violated"
                                     return env'

      --tau' <- flip evalStateT (0, ground') . unwrap . runMaybeT $ synthExpr env expr
      return ((var, ty, env') : results, extCtxt env var (Left ty))

-- Make type error report
mkReport :: (Id, Type, Maybe (Env TyOrDisc))
         -> String
mkReport (var, ty, Nothing) =
    "'" ++ var ++ "' does not type check, expected: " ++ pretty ty
        ++ ".\n Try annotating the types of functions or fixing a signature."
mkReport _ = ""

-- Checking on expressions
checkExpr :: Env TyOrDisc -> Type -> Expr -> MaybeT TypeState (Env TyOrDisc)
checkExpr gam (FunTy sig tau) (Abs x e) = checkExpr (extCtxt gam x (Left sig)) tau e

{-

[G] |- e : t
---------------------
[G]*r |- [e] : []_r t

-}

checkExpr gam (Box demand tau) (Promote e) = do
    gamF        <- discToFreshVars gam
    gam'        <- checkExpr gamF tau e
    gam `equalCtxts` gam'
    return gam'

checkExpr gam tau (App e1 e2) = do
    (sig, gam1) <- synthExpr gam e2
    gam2 <- checkExpr gam (FunTy sig tau) e1
    return (gam1 `ctxPlus` gam2)

checkExpr gam tau (Abs x e)             = illTyped "Checking abs"
checkExpr gam tau e = do
  (tau', gam') <- synthExpr gam e
  tyEq <- tau `typesEq` tau'
  if tyEq then return $ gam' else illTyped $ "Checking: (" ++ pretty e ++ "), "
                               ++ show tau ++ " != " ++ show tau'

typesEq :: Type -> Type -> MaybeT TypeState Bool
typesEq (FunTy t1 t2) (FunTy t1' t2') = do
  eq1 <- typesEq t1 t1'
  eq2 <- typesEq t2 t2'
  return (eq1 && eq2)
typesEq (ConT t) (ConT t') = do
  return (t == t')
typesEq (Box c t) (Box c' t') = do
  (fvCount, symbolic) <- get
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
synthExpr :: Env TyOrDisc -> Expr -> MaybeT TypeState (Type, Env TyOrDisc)

-- Variables
synthExpr gam (Var x) = do
   case lookup x gam of
     Nothing              -> illTyped $ "I don't know the type for " ++ show x
     Just (Left ty)       -> return (ty, gam)
     Just (Right (c, ty)) -> return (ty, replace gam x (Right (CPlus c one, ty)))

-- Constants (numbers)
synthExpr gam (Num _) = return (ConT TyInt, gam)

-- Application
synthExpr gam (App e e') = do
    (f, gam1) <- synthExpr gam e
    case f of
      (FunTy sig tau) -> do
         gam2 <- checkExpr gam sig e'
         return (tau, ctxPlus gam1 gam2)
      _ -> illTyped "Left-hand side of app is not a function type"

-- Promotion
synthExpr gam (Promote e) = do
   gamF <- discToFreshVars gam
   (t, gam') <- synthExpr gamF e
   gam `equalCtxts` gam'
   var <- liftTS freshVar
   return (Box (CVar var) t, gam')

-- Letbox
synthExpr gam (LetBox var t e1 e2) = do
   (tau, gam1) <- synthExpr (extCtxt gam var (Right (zero, t))) e2
   case lookup var gam1 of
       Just (Right (demand, t')) | t == t' -> do
            gam2 <- checkExpr gam1 (Box demand t) e1
            return (tau, ctxPlus gam1 gam2)
       _ -> illTyped $ "Context of letbox does not have " ++ var ++ " discharged"

-- BinOp
synthExpr gam (Binop op e e') = do
    (t, gam1)  <- synthExpr gam e
    (t', gam2) <- synthExpr gam e'
    case (t, t') of
        (ConT TyInt, ConT TyInt) -> return (ConT TyInt, ctxPlus gam1 gam2)
        _                        -> illTyped "Binary op does not have two int expressions"

synthExpr gam e = illTyped $ "General synth fail " ++ show e

equalCtxts :: Env TyOrDisc -> Env TyOrDisc -> MaybeT TypeState ()
equalCtxts env env' =
  if length env == length env'
  && map fst env == map fst env'
  && (lefts . map snd $ env) == (lefts . map snd $ env')
  && (rights . map snd $ env) == (rights . map snd $ env')
    then do
      (fv, symbolic) <- get
      let symbolic' = do
            (pred, vars) <- symbolic
            eqs <- return . foldr (&&&) true $ zipWith (makeEqual vars) env env'
            return (eqs &&& pred, vars)
      put (fv, symbolic')
    else illTyped "Environments do not match in size of types"

makeEqual freeVars (_, Left _) (_, Left _) = true
makeEqual freeVars (_, Right (c1, _)) (_, Right (c2, _)) = do
  compile c1 freeVars .== compile c2 freeVars
makeEqual _ _ _ = false

extractVars (_, Left _) = []
extractVars (_, Right (c, _)) = vars c

vars :: Coeffect -> [String]
vars (CVar v) = [v]
vars (CPlus n m) = vars n ++ vars m
vars (CTimes n m) = vars n ++ vars m
vars _ = []

compile :: Coeffect -> SolverVars -> SInteger
compile (Nat n) _ = (fromInteger . toInteger $ n) :: SInteger
compile (CVar v) vars = fromJust $ lookup v vars -- sInteger v
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
  thmRes <- liftio . prove $ do
                (pred, vars) <- symbolic
                return pred
  case thmRes of
     -- Tell the user if there was a hard proof error (e.g., if
     -- z3 is not installed/accessible).
     -- TODO: give more information
     ThmResult (ProofError _ msgs) -> illTyped $ "Prover error:" ++ unlines msgs
     _ -> if modelExists thmRes
           then
             case getModel thmRes of
               Right (False, ce :: [ Integer ] ) -> do
                                  illTyped $ "Returned model " ++ show ce ++ " - " ++ show thmRes
               Right (True, _) -> illTyped $ "Returned probable model."
               Left str        -> illTyped $ "Solver fail: " ++ str
           else return True

-- Generate a fresh alphanumeric variable name
freshVar :: TypeState String
freshVar = TS $ do
  (v, symbolic) <- get
  let prefix = ["a", "b", "c", "d"] !! (v `mod` 4)
  let cvar = prefix ++ show v
  let symbolic' = do
      (pred, vars) <- symbolic
      solverVar    <- exists cvar
      return (pred, (cvar, solverVar) : vars)
  put (v+1, symbolic')
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
      v <- freshVar
      return $ (id, Right (CVar v, t))
    toFreshVar c = return c