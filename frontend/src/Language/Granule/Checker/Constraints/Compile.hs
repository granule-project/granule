{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Granule.Checker.Constraints.Compile where


import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates


import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span

import Language.Granule.Utils


compileNatKindedTypeToCoeffectSafe :: Type -> Maybe Coeffect
compileNatKindedTypeToCoeffectSafe (TyInfix op t1 t2) = do
  t1' <- compileNatKindedTypeToCoeffectSafe t1
  t2' <- compileNatKindedTypeToCoeffectSafe t2
  case op of
    TyOpPlus  -> pure $ CPlus t1' t2'
    TyOpTimes -> pure $ CTimes t1' t2'
    TyOpExpon -> pure $ CExpon t1' t2'
    TyOpMinus -> pure $ CMinus t1' t2'
    TyOpJoin  ->   pure $ CJoin t1' t2'
    TyOpMeet  ->   pure $ CMeet t1' t2'
    _         -> Nothing
compileNatKindedTypeToCoeffectSafe (TyInt n) = pure $ CNat n
compileNatKindedTypeToCoeffectSafe (TyVar v) = pure $ CVar v
compileNatKindedTypeToCoeffectSafe _ = Nothing


compileNatKindedTypeToCoeffect :: (?globals :: Globals) => Span -> Type -> Checker Coeffect
compileNatKindedTypeToCoeffect s tinfix@(TyInfix op _ _) =
  maybe (throw NotImplemented{ errLoc = s, errDesc = "I don't know how to compile binary operator " <> pretty op })
        pure (compileNatKindedTypeToCoeffectSafe tinfix)
compileNatKindedTypeToCoeffect s t =
  maybe (throw KindError{errLoc = s, errTy = t, errK = kNat }) pure (compileNatKindedTypeToCoeffectSafe t)


compileTypeConstraintToConstraint ::
    (?globals :: Globals) => Span -> Type -> Checker Pred
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
    _ -> throw NotImplemented{ errLoc = s, errDesc = "I don't know how to compile binary operator " <> pretty op }

compileTypeConstraintToConstraint s t =
  throw NotImplemented{ errLoc = s, errDesc = "I don't know how to compile a constraint " <> prettyQuoted t }


-----------------------
-- Predicate Helpers --
-----------------------


compileAndAddPredicate :: (?globals :: Globals) => Span -> Type -> Checker ()
compileAndAddPredicate sp ty =
  compileTypeConstraintToConstraint sp ty >>= addPredicate


-- | Constrain the typescheme with the given predicates.
constrainTysWithPredicates :: [Type] -> TypeScheme -> TypeScheme
constrainTysWithPredicates preds (Forall sp binds constrs ty) = Forall sp binds (constrs <> preds) ty
