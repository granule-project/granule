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
    (?globals :: Globals) => Span -> Type -> Checker Type
compileNatKindedTypeToCoeffect s t = compileNatKindedTypeToCoeffectAtType s t (TyCon $ mkId "Nat")

-- Take a type (second parameter) and convert it to a coeffect at a particular
-- coeffect type (third parameter)
compileNatKindedTypeToCoeffectAtType ::
    (?globals :: Globals) => Span -> Type -> Type -> Checker Type

compileNatKindedTypeToCoeffectAtType s (TyInfix op t1 t2) coeffTy = do
  t1' <- compileNatKindedTypeToCoeffectAtType s t1 coeffTy
  t2' <- compileNatKindedTypeToCoeffectAtType s t2 coeffTy
  return $ TyInfix op t1' t2'
compileNatKindedTypeToCoeffectAtType _ t@(TyInt _) coeffTy = return t
compileNatKindedTypeToCoeffectAtType _ t@(TyVar _) coeffTy = return t
compileNatKindedTypeToCoeffectAtType _ (TyCon (internalName -> "Pure")) (TyCon (internalName -> "Nat")) =
  return $ TyInt 0
compileNatKindedTypeToCoeffectAtType s (TySig t _) coeffTy =
  compileNatKindedTypeToCoeffectAtType s t coeffTy
compileNatKindedTypeToCoeffectAtType s t coeffTy = do
  throw KindError{errLoc = s, errTy = t, errK = KPromote coeffTy }
