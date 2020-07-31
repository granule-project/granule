{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Granule.Checker.Constraints.CompileNatKinded where

import Language.Granule.Checker.Monad

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span

import Language.Granule.Utils

-- Take a type and convert it to a coeffect of coeffect type Nat
-- NOTE: this will disappear at some point when we unify the syntax more
compileNatKindedTypeToCoeffect ::
    (?globals :: Globals) => Span -> Type -> Checker Coeffect
compileNatKindedTypeToCoeffect s t = compileNatKindedTypeToCoeffectAtType s t (TyCon $ mkId "Nat")

-- Take a type (second parameter) and convert it to a coeffect at a particular
-- coeffect type (third parameter)
compileNatKindedTypeToCoeffectAtType ::
    (?globals :: Globals) => Span -> Type -> Type -> Checker Coeffect

compileNatKindedTypeToCoeffectAtType s (TyInfix op t1 t2) coeffTy = do
  t1' <- compileNatKindedTypeToCoeffectAtType s t1 coeffTy
  t2' <- compileNatKindedTypeToCoeffectAtType s t2 coeffTy
  case op of
    TyOpPlus  -> return $ CPlus t1' t2'
    TyOpTimes -> return $ CTimes t1' t2'
    TyOpExpon -> return $ CExpon t1' t2'
    TyOpMinus -> return $ CMinus t1' t2'
    TyOpJoin  -> return $ CJoin t1' t2'
    TyOpMeet  -> return $ CMeet t1' t2'
    _ -> undefined
compileNatKindedTypeToCoeffectAtType _ (TyInt 1) coeffTy =
  return $ COne coeffTy
compileNatKindedTypeToCoeffectAtType _ (TyInt 0) coeffTy =
  return $ CZero coeffTy
compileNatKindedTypeToCoeffectAtType _ (TyInt n) coeffTy =
  return $ CNat n
compileNatKindedTypeToCoeffectAtType _ (TyVar v) coeffTy =
  return $ CVar v
compileNatKindedTypeToCoeffectAtType _ (TyCon (internalName -> "Pure")) (TyCon (internalName -> "Nat")) =
  return $ CNat 0
compileNatKindedTypeToCoeffectAtType s t coeffTy =
  throw $ KindError{errLoc = s, errTy = t, errK = KPromote coeffTy }
