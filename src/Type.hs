{-# LANGUAGE FlexibleInstances #-}

module Type where

import Expr
import Eval hiding (Env, empty, extend)
import Data.List
import Debug.Trace

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

-- Extend the environment
extend :: Env TyOrDisc -> Id -> TyOrDisc -> Env TyOrDisc
extend env id (Left t)  = (id, Left t) : env
extend env id (Right (c, t)) =
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
  ctxPlus env1 (extend env2 i v)

instance Pretty (Type, Env TyOrDisc) where
  pretty (t, env) = pretty t

-- Checking (top-level)
check :: [Def] -> Either String Bool
check defs =
    if (and . map (\(_, _, _, check) -> case check of Just _ -> True; Nothing -> False) $ results)
    then Right True
    else Left $ intercalate "\n" (map mkReport results)
  where
    (results, _) = foldl checkDef ([], empty) defs
    checkDef (results, env) (Def var expr ty) =
      ((var, ty, synthExpr env expr, checkExpr env ty expr) : results, extend env var (Left ty))

-- Make type error report
mkReport :: (Id, Type, Maybe (Type, Env TyOrDisc), Maybe (Env TyOrDisc))
         -> String
mkReport (var, ty, tyInferred, Nothing) =
    var ++ " does not type check, expected: " ++ pretty ty ++ ", got: " ++ pretty tyInferred
        ++ ". Try annotating the types of functions"
-- mkReport (var, ty, tyInference,
mkReport _ = ""

-- Checking on expressions
checkExpr :: Env TyOrDisc -> Type -> Expr -> Maybe (Env TyOrDisc)
checkExpr gam (FunTy sig tau) (Abs x e) = checkExpr (extend gam x (Left sig)) tau e

--checkExpr gam (Box demand tau) (Promotion e) = do
--    (sig, gam) <- checkExpr (

checkExpr gam tau (App e1 e2) = do
    (sig, gam1) <- synthExpr gam e2
    gam2 <- checkExpr gam (FunTy sig tau) e1
    return (gam1 `ctxPlus` gam2)
checkExpr gam tau (Abs x e)             = Nothing
checkExpr gam tau e = do
  (tau', gam') <- synthExpr gam e
  if tau == tau' then return $ gam' else Nothing

-- Synthesise on expressions
synthExpr :: Env TyOrDisc -> Expr -> Maybe (Type, Env TyOrDisc)

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
    show f `trace` case f of
      (FunTy sig tau) -> do
         gam2 <- checkExpr gam sig e'
         return (tau, ctxPlus gam1 gam2)
      _ -> Nothing

-- Promotion
synthExpr gam (Promote e) = do
   (t, env) <- synthExpr (derelictAll gam) e
   return (Box one t, env) -- Wrong

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