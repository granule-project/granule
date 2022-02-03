{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}

-- | Provides helpers for compiling constraints
module Language.Granule.Checker.Constraints.Compile
   (compileTypeConstraintToConstraint
  , enforceConstraints
  , dischargedTypeConstraints) where

import Control.Monad.State.Strict

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Kinding (checkKind, synthKind)

import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

-- import Language.Granule.Checker.Types

import Language.Granule.Utils

compileTypeConstraintToConstraint ::
    (?globals :: Globals) => Span -> Type -> Checker (Either Pred Type)
compileTypeConstraintToConstraint s (TyInfix op t1 t2) = do
  (k, _, _) <- synthKind s t1
  (result, putChecker) <- peekChecker (checkKind s t2 k)
  case result of
    Right _ -> do
      putChecker
      pred <- compileAtType s op t1 t2 k
      return $ Left pred
    Left _ ->
      case k of
        TyVar v -> do
          st <- get
          case lookup v (tyVarContext st) of
            Just (_, ForallQ) | isGenericCoeffectExpression t2 -> do
              pred <- compileAtType s op t1 t2 (TyVar v)
              return $ Left pred

            _ -> throw $ UnificationError s t1 t2
        _ -> throw $ UnificationError s t1 t2

-- Some other kind of constraint that has to be registered for this equation
compileTypeConstraintToConstraint s t =
  return $ Right t

compileAtType :: (?globals :: Globals) => Span -> TypeOperator -> Type -> Type -> Type -> Checker Pred
compileAtType s op c1 c2 coeffTy = do
  case op of
    TyOpEq -> return $ Con (Eq s c1 c2 coeffTy)
    TyOpNotEq -> return $ Con (Neq s c1 c2 coeffTy)
    TyOpLesserNat -> return $ Con (Lt s c1 c2)
    TyOpGreaterNat -> return $ Con (Gt s c1 c2)
    TyOpLesserEq -> return $ Con (ApproximatedBy s c1 c2 coeffTy)
    TyOpGreaterEq -> return $ Con (ApproximatedBy s c2 c1 coeffTy)
    TyOpLesserEqNat -> return $ Con (LtEq s c1 c2)
    TyOpGreaterEqNat -> return $ Con (GtEq s c1 c2)
    _ -> error $ pretty s <> ": I don't know how to compile binary operator " <> pretty op


-- Given a list of type constraints (things to the left of a =>)
-- registers those which are graded things as predicates
-- and returns those which are 'regular' type constraints
enforceConstraints :: (?globals :: Globals) => Span -> [Type] -> Checker [Type]
enforceConstraints s [] = return []
enforceConstraints s (t:ts) = do
  sx <- compileTypeConstraintToConstraint s t
  case sx of
    Left pred -> do
      addPredicate pred
      enforceConstraints s ts

    Right t -> do
      ts' <- enforceConstraints s ts
      return $ t : ts'

-- Match provided constraints (assumptions) against wanted constraints /
-- see if the wanted constraints are already satisfied
dischargedTypeConstraints :: Span -> [Type] -> [Type] -> Checker ()
dischargedTypeConstraints s provided [] = return ()
dischargedTypeConstraints s provided (w : ws) =
  if w `elem` provided
    then dischargedTypeConstraints s provided ws
    else do
      b <- isDefinedConstraint w
      if b
        then dischargedTypeConstraints s provided ws
        else throw $ TypeConstraintNotSatisfied s w

-- TODO: provide some way to define this related with user syntax
isDefinedConstraint :: Type -> Checker Bool
isDefinedConstraint _ = return False