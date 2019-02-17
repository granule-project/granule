{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Granule.Checker.Constraints.Compile where

import Control.Monad.Trans.Maybe

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Errors

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span

import Language.Granule.Utils

compileNatKindedTypeToCoeffect :: (?globals :: Globals) => Span -> Type -> MaybeT Checker Coeffect
compileNatKindedTypeToCoeffect s (TyInfix op t1 t2) = do
  t1' <- compileNatKindedTypeToCoeffect s t1
  t2' <- compileNatKindedTypeToCoeffect s t2
  case op of
    TyOpPlus  -> return $ CPlus t1' t2'
    TyOpTimes -> return $ CTimes t1' t2'
    TyOpExpon -> return $ CExpon t1' t2'
    TyOpMinus -> return $ CMinus t1' t2'
    TyOpJoin  -> return $ CJoin t1' t2'
    TyOpMeet  -> return $ CMeet t1' t2'
    _ -> undefined

compileNatKindedTypeToCoeffect _ (TyInt n) =
  return $ CNat n
compileNatKindedTypeToCoeffect _ (TyVar v) =
  return $ CVar v
compileNatKindedTypeToCoeffect s t =
  halt $ KindError (Just s) $ "Type `" <> pretty t <> "` does not have kind `Nat`"

compileTypeConstraintToConstraint ::
    (?globals :: Globals) => Span -> Type -> MaybeT Checker Pred
compileTypeConstraintToConstraint s (TyInfix op t1 t2) = do
  c1 <- compileNatKindedTypeToCoeffect s t1
  c2 <- compileNatKindedTypeToCoeffect s t2
  case op of
    TyOpEq -> return $ Con (Eq s c1 c2 (TyCon $ mkId "Nat"))
    TyOpNotEq -> return $ Con (Neq s c1 c2 (TyCon $ mkId "Nat"))
    TyOpLesser -> return $ Con (Lt s c1 c2)
    TyOpGreater -> return $ Con (Gt s c1 c2)
    TyOpLesserEq -> return $ Disj [Con $ Lt s c1 c2, Con $ Eq s c1 c2 (TyCon $ mkId "Nat")]
    TyOpGreaterEq -> return $ Disj [Con $ Gt s c1 c2, Con $ Eq s c1 c2 (TyCon $ mkId "Nat")]
    _ -> halt $ GenericError (Just s) $ "I don't know how to compile binary operator " <> pretty op

compileTypeConstraintToConstraint s t =
  halt $ GenericError (Just s) $ "I don't know how to compile a constraint `" <> pretty t <> "`"
