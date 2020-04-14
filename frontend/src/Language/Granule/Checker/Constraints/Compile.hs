{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Granule.Checker.Constraints.Compile where

import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Coeffects
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span

import Control.Monad.State.Strict
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


compileTypeConstraintToConstraint ::
    (?globals :: Globals) => Span -> Type -> Checker Pred
compileTypeConstraintToConstraint s (TyInfix op t1 t2) = do
  k1 <- inferKindOfType s t1
  k2 <- inferKindOfType s t2
  jK <- joinKind k1 k2
  case jK of
    Just (k, _) -> do
      case demoteKindToType k of
        Just coeffTy -> compileAtType s op t1 t2 coeffTy
        _ ->  error $ pretty s <> ": I don't know how to compile at kind " <> pretty k
    Nothing ->
      case k1 of
        KVar v -> do
          st <- get
          case lookup v (tyVarContext st) of
            Just (_, ForallQ) | isGenericCoeffectExpression t2 -> compileAtType s op t1 t2 (TyVar v)
            _                                                  -> throw $ UnificationError s t1 t2
        _ -> case k2 of
              KVar v -> do
                st <- get
                case lookup v (tyVarContext st) of
                  Just (_, ForallQ) | isGenericCoeffectExpression t1 -> compileAtType s op t1 t2 (TyVar v)
                  _                                                  -> throw $ UnificationError s t1 t2
              _ -> throw $ UnificationError s t1 t2
compileTypeConstraintToConstraint s t =
  error $ pretty s <> ": I don't know how to compile a constraint `" <> pretty t <> "`"

compileAtType :: (?globals :: Globals) => Span -> TypeOperator -> Type -> Type -> Type -> Checker Pred
compileAtType s op t1 t2 coeffTy = do
  c1 <- compileNatKindedTypeToCoeffectAtType s t1 coeffTy
  c2 <- compileNatKindedTypeToCoeffectAtType s t2 coeffTy
  case op of
    TyOpEq -> return $ Con (Eq s c1 c2 coeffTy)
    TyOpNotEq -> return $ Con (Neq s c1 c2 coeffTy)
    TyOpLesser -> return $ Con (Lt s c1 c2)
    TyOpGreater -> return $ Con (Gt s c1 c2)
    TyOpLesserEq -> return $ Con (LtEq s c1 c2)
    TyOpGreaterEq -> return $ Con (GtEq s c1 c2)
    _ -> error $ pretty s <> ": I don't know how to compile binary operator " <> pretty op