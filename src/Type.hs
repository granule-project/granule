{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, FlexibleContexts #-}

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
  mult (Nat n) (Nat m) = Nat (n * m)
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
        else error $ "Typelash for discharged variable"
    Just (Left _) -> error $ "Typelash for discharged variable"
    Nothing -> (id, Right (c, t)) : env

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


ctxPlus :: Env TyOrDisc -> Env TyOrDisc -> Env TyOrDisc
ctxPlus [] env2 = env2
ctxPlus ((i, v) : env1) env2 =
  ctxPlus env1 (extCtxt env2 i v)

instance Pretty (Type, Env TyOrDisc) where
  pretty (t, env) = pretty t

ground = forAll_ $ \(x :: SInt64) -> true :: SBool
falsity = forAll_ $ \(x :: SInt64) -> false :: SBool

-- Checking (top-level)
check :: [Def] -> IO (Either String Bool)
check defs = do
    (results, _) <- foldM checkDef ([], empty) defs
    if (and . map (\(_, _, _, check) -> isJust check) $ results)
      then return . Right $ True
      else return . Left  $ intercalate "\n" (map mkReport results)
  where
    checkDef (results, env) (Def var expr ty) = do
      env' <- flip evalStateT (0, ground) . unwrap . runMaybeT $ checkExpr env ty expr
      tau' <- flip evalStateT (0, ground) . unwrap . runMaybeT $ synthExpr env expr
      return ((var, ty, tau', env') : results, extCtxt env var (Left ty))

-- Make type error report
mkReport :: (Id, Type, Maybe (Type, Env TyOrDisc), Maybe (Env TyOrDisc))
         -> String
mkReport (var, ty, tyInferred, Nothing) =
    var ++ " does not type check, expected: " ++ pretty ty ++ ", got: " ++ pretty tyInferred
        ++ ". Try annotating the types of functions"
-- mkReport (var, ty, tyInference,
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
    traceShowM $ gam ++ gam'
    state <- gam `equalCtxts` gam'
    if state
     then return gam'
     else illTyped $ "Checking typed of a promote as [" ++ show tau
                     ++ "] " ++ show demand

{-    (sig, gam') <- synthExpr gamF e
    if (sig == tau)
      then do solveConstraints; return gam'
      else illTyped -}

checkExpr gam tau (App e1 e2) = do
    (sig, gam1) <- synthExpr gam e2
    gam2 <- checkExpr gam (FunTy sig tau) e1
    return (gam1 `ctxPlus` gam2)
checkExpr gam tau (Abs x e)             = illTyped "Checking abs"
checkExpr gam tau e = do
  (tau', gam') <- synthExpr gam e
  if tau == tau' then return $ gam' else illTyped $ "Checking: (" ++ pretty e ++ "), "
                                           ++ show tau ++ " != " ++ show tau'


liftm :: Maybe a -> MaybeT TypeState a
liftm = MaybeT . return

-- Synthesise on expressions
synthExpr :: Env TyOrDisc -> Expr -> MaybeT TypeState (Type, Env TyOrDisc)

-- Variables
synthExpr gam (Var x) = do
   t <- liftm $ lookup x gam
   case t of
    Left ty       -> return (ty, gam)
    Right (c, ty) -> return (ty, replace gam x (Right (one, ty)))

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
   state <- gam `equalCtxts` gam'
   var <- liftTS freshVar
   if state
    then return (Box (CVar var) t, gam')
    else illTyped $ "Equality fail on contexts in type synth for promotion"

-- Letbox
synthExpr gam (LetBox var t e1 e2) = do
   (tau, gam1) <- synthExpr (extCtxt gam var (Right (zero, t))) e2
   case lookup var gam1 of
       Just (Right (demand, t')) | t == t' -> do
            traceShowM gam1
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

synthExpr gam _ = illTyped "General synth fail"

equalCtxts :: Env TyOrDisc -> Env TyOrDisc -> MaybeT TypeState Bool
equalCtxts env env' =
  if length env == length env' && map fst env == map fst env'
                               && (lefts . map snd $ env) == (lefts . map snd $ env')
                               && (rights . map snd $ env) == (rights . map snd $ env')
    then liftio $ do
           let freeVarNames = concatMap extractVars (env ++ env')
           traceShowM freeVarNames
           let pred = do
                freeVars <- mkFreeVarsMap freeVarNames
                return $ foldr (&&&) true $ zipWith (makeEqual freeVars) env env'
           thmRes <- prove pred
           case thmRes of
                 -- Tell the user if there was a hard proof error (e.g., if
                 -- z3 is not installed/accessible).
                 -- TODO: give more information
                 ThmResult (ProofError _ msgs) -> fail $ unlines msgs
                 _ -> if modelExists thmRes
                      then
                        case getModel thmRes of
                          Right (False, ce :: [ Int64 ]) -> do
                            putStrLn $ show $ zip freeVarNames ce
                            return False
                          Right (True, _) -> fail "Returned probable model."
                          Left str -> fail str
                      else (show thmRes) `trace` return True
    else illTyped "Environments do not match in size of types"

--makeEqual :: (Id, TyOrDisc) -> (Id, TyOrDisc) -> Symbolic SBool
makeEqual freeVars (_, Left _) (_, Left _) = true
makeEqual freeVars (_, Right (c1, _)) (_, Right (c2, _)) = do
  compile c1 freeVars .== compile c2 freeVars
  --forAll (vars c1 ++ vars c2) (compile c1 .== compile c2)
makeEqual _ _ _ = false

mkFreeVarsMap vs = do
  fvars <- mkFreeVars (length vs) -- (mkFreeVars vs :: Symbolic [ SInt64 ])
  return $ zip vs fvars

extractVars (_, Left _) = []
extractVars (_, Right (c, _)) = vars c

vars :: Coeffect -> [String]
vars (CVar v) = [v]
vars (CPlus n m) = vars n ++ vars m
vars (CTimes n m) = vars n ++ vars m
vars _ = []

compile :: Coeffect -> [(String, SInteger)] -> SInteger
compile (Nat n) _ = (fromInteger . toInteger $ n) :: SInteger
compile (CVar v) vars = fromJust $ lookup v vars -- sInteger v
compile (CPlus n m) vars = compile n vars + compile m vars
compile (CTimes n m) vars = compile n vars * compile m vars

illTyped :: String -> MaybeT TypeState a
illTyped s = liftio (putStrLn s) >> MaybeT (return Nothing)

type VarCounter  = Int
data TypeState a = TS { unwrap :: StateT (VarCounter, Predicate) IO a }

liftio :: forall a . IO a -> MaybeT TypeState a
liftio m = MaybeT (TS ((lift (m >>= (return . Just))) :: StateT (VarCounter, Predicate) IO (Maybe a)))

instance Monad TypeState where
  return = TS . return
  (TS x) >>= f = TS (x >>= (unwrap . f))

instance Functor TypeState where
  fmap f (TS x) = TS (fmap f x)

instance Applicative TypeState where
  pure    = return
  f <*> x = f >>= \f' -> x >>= \x' -> return (f' x')

--solveConstraints = return ()

-- Generate a fresh alphanumeric variable name
freshVar :: TypeState String
freshVar = TS $ do
  (v, pred) <- get
  put (v+1, pred)
  let prefix = ["a", "b", "c", "d"] !! (v `mod` 4)
  return $ prefix ++ show v

liftTS :: TypeState a -> MaybeT TypeState a
liftTS t = MaybeT $ t >>= (return . Just)

-- Replace all top-level discharged coeffects
discToFreshVars :: Env TyOrDisc -> MaybeT TypeState (Env TyOrDisc)
discToFreshVars env = MaybeT $ mapM toFreshVar env >>= (return . Just)
  where
    toFreshVar (id, Right (c, t)) = do
      v <- freshVar
      return $ (id, Right (CVar v, t))
    toFreshVar c = return c