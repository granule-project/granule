{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Checker.Types where

import Syntax.Expr
import Syntax.Pretty
import Context
import Data.List

import Control.Monad.Trans.Maybe
import Control.Monad.State.Strict

import Checker.Coeffects
import Checker.Constraints
import Checker.Environment

-- Given a pattern and its type, construct the binding environment
-- for that pattern
ctxtFromTypedPattern
   :: Bool -> Span -> Type -> Pattern -> MaybeT Checker (Maybe [(Id, TyOrDisc)])
ctxtFromTypedPattern _ _ _              (PWild _)      = return $ Just []
ctxtFromTypedPattern _ _ t              (PVar _ v)     = return $ Just [(v, Left t)]
ctxtFromTypedPattern _ _ (ConT "Int")   (PInt _ _)     = return $ Just []
ctxtFromTypedPattern _ _ (ConT "Float") (PFloat _ _)   = return $ Just []
ctxtFromTypedPattern _ _ (Box c t)      (PBoxVar _ v)  = return $  Just [(v, Right (c, t))]
ctxtFromTypedPattern _ _ (ConT "Bool")  (PConstr _ "True")  = return $ Just []
ctxtFromTypedPattern _ _ (ConT "Bool")  (PConstr _ "False") = return $ Just []
ctxtFromTypedPattern _ _ (ConT "List")  (PConstr _ "Cons")  = return $ Just []
ctxtFromTypedPattern _ _ (TyApp (TyApp (ConT "List") _) _) (PConstr _ "Nil") = return $ Just []
ctxtFromTypedPattern dbg s (TyApp (TyApp (ConT "List") n) t) (PApp _ (PApp _ (PConstr _ "Cons") p1) p2) = do
  bs1 <- ctxtFromTypedPattern dbg s t p1
  sizeVar <- freshVar "in"
  let sizeVarInc = CPlus (CVar sizeVar) (CNat Discrete 1)
  let kind       = CConstr "Nat="
  -- Update coeffect-kind environment
  checkerState <- get
  put $ checkerState { ckenv = (sizeVar, (kind, ExistsQ)) : ckenv checkerState }
  -- Generate equality constraint
  case n of
    TyVar v -> addConstraint $ Eq s (CVar v) sizeVarInc kind
    TyInt n -> addConstraint $ Eq s (CNat Discrete n) sizeVarInc kind
  bs2 <- ctxtFromTypedPattern dbg s (TyApp (TyApp (ConT "List") (TyVar sizeVar)) t) p2
  return $ bs1 >>= (\bs1' -> bs2 >>= (\bs2' -> Just (bs1' ++ bs2')))
ctxtFromTypedPattern _ _ t p = return Nothing

-- Check whether two types are equal, and at the same time
-- generate coeffect equality constraints
--
-- The first argument is taken to be possibly approximated by the second
-- e.g., the first argument is inferred, the second is a specification
-- being checked against
equalTypes :: Bool -> Span -> Type -> Type -> MaybeT Checker Bool
equalTypes dbg s (FunTy t1 t2) (FunTy t1' t2') = do
  eq1 <- equalTypes dbg s t1' t1 -- contravariance
  eq2 <- equalTypes dbg s t2 t2' -- covariance
  return (eq1 && eq2)

equalTypes _ _ (ConT con) (ConT con') = return (con == con')

equalTypes dbg s (Diamond ef t) (Diamond ef' t') = do
  eq <- equalTypes dbg s t t'
  if ef == ef'
    then return eq
    else do
      illGraded s $ "Effect mismatch: " ++ pretty ef
                  ++ " not equal to " ++ pretty ef'
      halt

equalTypes dbg s (Box c t) (Box c' t') = do
  -- Debugging
  dbgMsg dbg $ pretty c ++ " == " ++ pretty c'
  dbgMsg dbg $ "[ " ++ show c ++ " , " ++ show c' ++ "]"
  -- Unify the coeffect kinds of the two coeffects
  kind <- mguCoeffectKinds s c c'
  addConstraint (Leq s c c' kind)
  equalTypes dbg s t t'

equalTypes dbg s (TyApp t1 t2) (TyApp t1' t2') = do
  one <- equalTypes dbg s t1 t1'
  two <- equalTypes dbg s t2 t2'
  return (one && two)

equalTypes dbg s (TyInt n) (TyVar m) = do
  addConstraint (Eq s (CNat Discrete n) (CVar m) (CConstr "Nat="))
  return True

equalTypes dbg s (TyVar n) (TyInt m) = do
  addConstraint (Eq s (CVar n) (CNat Discrete m) (CConstr "Nat="))
  return True

equalTypes dbg s (TyVar n) (TyVar m) = do
  addConstraint (Eq s (CVar n) (CVar m) (CConstr "Nat="))
  return True

equalTypes dbg s (TyInt n) (TyInt m) = do
  return (n == m)

equalTypes _ s t1 t2 =
  illTyped s $ "Expected '" ++ pretty t2 ++ "' but got '" ++ pretty t1 ++ "'"


instance Pretty (Type, Env TyOrDisc) where
    pretty (t, _) = pretty t

instance Pretty (Id, TyOrDisc) where
    pretty (v, ty) = v ++ " : " ++ pretty ty

instance Pretty TyOrDisc where
    pretty (Left ty) = pretty ty
    pretty (Right (c, ty)) = "|" ++ pretty ty ++ "|." ++ pretty c

instance Pretty (Env TypeScheme) where
   pretty xs = "{" ++ intercalate "," (map pp xs) ++ "}"
     where pp (var, t) = var ++ " : " ++ pretty t

instance Pretty (Env TyOrDisc) where
   pretty xs = "{" ++ intercalate "," (map pp xs) ++ "}"
     where pp (var, Left t) = var ++ " : " ++ pretty t
           pp (var, Right (c, t)) = var ++ " : .[" ++ pretty t ++ "]. " ++ pretty c
