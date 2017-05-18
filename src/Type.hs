module Type where

import Expr
import Eval hiding (Env, empty, extend)
import Data.List

type TyOrDisc c = Either (Type c) (c, Type c)

class Semiring c where
  plus  :: c -> c -> c
  times :: c -> c -> c
  one   :: c
  zero  :: c

empty = []
type Env t = [(Id, t)]

-- replace an item in an environment
replace :: Env a -> Id -> a -> Env a
replace [] id v
  = [(id, v)]
replace ((id', _):env) id v | id == id'
  = (id', v) : env
replace (x, env) id v
  = x : replace env id v

-- Extend the environment
extend :: Semiring c => Env (TyOrDisc c) -> Id -> TyOrDisc c -> Env (TyOrDisc c)
extend env id (Left t)  = (id, Left t) : env
extend env id (Right (c, t)) =
  case (lookup env id) of
    Just (Right (c', t')) ->
        if t == t'
        then replace (Right (c `plus` c', t')) env
        else error $ "Type clash for discharged variable"
    Just (Left _) -> error $ "Type clash for discharged variable"
    Nothing -> (id, Right (c, t)) : env

-- Given an environment, derelict and discharge all variables which are not discharged
derelictAndMultAll :: Semiring c => c -> Env (TyOrDisc c) -> Env (TyOrDisc c)
derelictAndMultAll _ [] = []
derelictAndMultAll c ((id, Left t) : env) = (id, Right (c, t)) : derelictAndMultAll env
derelictAndMultAll c ((id, Right c' t) : env) = (id, Right (c `mult` c', t)) : derelictAndMultAll env

derelictAll :: Semiring c => Env (TyOrDisc c) -> Env (TyOrDisc c)
derelictAll _ [] = []
derelictAll c ((id, Left t) : env) = (id, Right (zero, t)) : derelictAll env
derelictAll c (e : env) = e : derelictAll env


ctxPlus :: Semiring c => Env (TyOrDisc c) -> Env (TyOrDisc c) -> Env (TyOrDisc c)
ctxPlus [] env2 = env2
ctxPlus ((i, v) : env1) env2 =
  ctxPlus env1 (extend env2 i v)

-- Checking (top-level)
check :: Semiring c => [Def c] -> Either String Bool
check defs =
    if (and . map (\(_, _, _, flag) -> flag) $ results)
    then Right True
    else Left $ intercalate "\n" (map mkReport results)
  where
    (results, _) = foldl checkDef ([], empty) defs
    checkDef (results, env) (Def var expr ty) =
      ((var, ty, synthExpr env expr, checkExpr env ty expr) : results, extend env var (Left ty))

-- Make type error report
mkReport (var, ty, _, Nothing) =
    var ++ " does not type check, expected: " ++ pretty ty -- ++ ", got: " ++ pretty tyInferred
        ++ ". Try annotating the types of functions"
-- mkReport (var, ty, tyInference,
mkReport _ = ""

-- Checking on expressions
checkExpr :: (Semiring c, Eq c) =>
             Env (TyOrDisc c) -> Type c -> Expr c -> Maybe (Env (TyOrDisc c))
checkExpr gam (FunTy sig tau) (Abs x e) = checkExpr (extend gam x (Left sig)) tau e
checkExpr gam tau (App e1 e2) = do
    (sig, gam1) <- synthExpr gam e2
    gam2 <- checkExpr gam (FunTy sig tau) e1
    return (gam1 `ctxPlus` gam2)

checkExpr gam tau (Abs x e)             = Nothing
checkExpr gam tau e = do
  (tau', gam') <- synthExpr gam e
  if tau == tau' then return $ gam' else Nothing

-- Synthesise on expressions
synthExpr :: (Eq c, Semiring c) =>
             Env (TyOrDisc c) -> Expr c -> Maybe (Type c, Env (TyOrDisc c))

-- Variables
synthExpr gam (Var x) = do
   t <- lookup x gam
   return $ case t of
    Left ty       -> (ty, gam)
    Right (c, ty) -> (ty, replace gam x (Right (one, ty)))

-- Constants (numbers)
synthExpr gam (Num _) = return (ConT TyInt, gam)

-- Application
synthExpr gam (App e e') = do
    (f, gam1) <- synthExpr gam e
    case f of
      (FunTy sig tau) -> do
         gam2 <- checkExpr gam sig e'
         return (tau, ctxPlus gam1 gam2)
      _ -> Nothing

-- Promotion
synthExpr gam (Promote e) = do
   synthExpr (derelictAll gam) e

-- Letbox
synthExpr gam (LetBox var t e1 e2) = do
   (tau, gam1) <- synthExpr (extend gam var (Right (zero, t))) e2
   case lookup var gam1 of
       Just (Right (demand, t')) | t == t' -> do
            gam2 <- checkExpr gam1 (Box demand t) e1
            return (tau, ctxPlus gam1 gam2)
       _ -> Nothing

-- BinOp
synthExpr gam (Binop op e e') = do
    (t, gam1)  <- synthExpr gam e
    (t', gam2) <- synthExpr gam e'
    case (t, t') of
        (ConT TyInt, ConT TyInt) -> Just $ (ConT TyInt, ctxPlus gam1 gam2)
        _                        -> Nothing

synthExpr gam _ = Nothing


{-
checkAlt :: Env Type -> Expr -> Type -> Maybe (Env Type)
checkAlt env e tau = do
  (tau', env') <- synthAlt env e
  if tau == tau'
    then Just env'
    else Nothing

synthAlt :: Env Type -> Expr -> Maybe (Type, Env Type)
synthAlt env (Var x) = Just (env x, env)
synthAlt env (Num _) = Just (ConT TyInt, env)
synthAlt env (App e1 e2) = do
    (t, env1) <- synthAlt env e2
    case t of
      (FunTy sig tau) ->
          case checkAlt env1 e2 sig of
             Just env2 -> Just (tau, env2)
             Nothing   -> Nothing
synthAlt env (Binop op e1 e2) = do
    env1 <- checkAlt env e1 (ConT TyInt)
    env2 <- checkAlt env1 e2 (ConT TyInt)
    return $ (ConT TyInt, env2)
synthAlt env (Abs x e) = do
   -}
