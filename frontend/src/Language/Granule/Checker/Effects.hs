{- Deals with effect algebras -}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Effects where

import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Primitives (setLike)
import Language.Granule.Checker.Variables

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span

import Language.Granule.Utils

import Data.List (nub)

-- `isEffUnit sp effTy eff` checks whether `eff` of effect type `effTy`
-- is equal to the unit element of the algebra.
isEffUnit :: (?globals :: Globals) => Span -> Type -> Type -> Checker Bool
isEffUnit s effTy eff =
    case effTy of
        -- Nat case
        TyCon (internalName -> "Nat") -> do
            nat <- compileNatKindedTypeToCoeffect s eff
            addConstraint (Eq s (CNat 0) nat (TyCon $ mkId "Nat"))
            return True
        -- Session singleton case
        TyCon (internalName -> "Com") -> do
            return True
        -- IO set case
        -- Any union-set effects, like IO
        TyCon c | setLike c ->
            case eff of
                (TySet []) -> return True
                _          -> return False
        -- Unknown
        _ -> throw $ UnknownResourceAlgebra { errLoc = s, errTy = eff, errK = KPromote effTy }

-- `effApproximates s effTy eff1 eff2` checks whether `eff1 <= eff2` for the `effTy`
-- resource algebra
effApproximates :: (?globals :: Globals) => Span -> Type -> Type -> Type -> Checker Bool
effApproximates s effTy eff1 eff2 =
    case effTy of
        -- Nat case
        TyCon (internalName -> "Nat") -> do
            nat1 <- compileNatKindedTypeToCoeffect s eff1
            nat2 <- compileNatKindedTypeToCoeffect s eff2
            addConstraint (ApproximatedBy s nat1 nat2 (TyCon $ mkId "Nat"))
            return True
        -- Session singleton case
        TyCon (internalName -> "Com") -> do
            return True
        -- IO set case
        -- Any union-set effects, like IO
        TyCon c | setLike c ->
            case eff1 of
                (TyCon (internalName -> "Pure")) -> return True
                (TySet efs1) ->
                    case eff2 of
                        (TySet efs2) ->
                            -- eff1 is a subset of eff2
                            return $ all (\ef1 -> ef1 `elem` efs2) efs1
                        _ -> return False
                _ -> return False
        -- Unknown
        _ -> throw $ UnknownResourceAlgebra { errLoc = s, errTy = eff1, errK = KPromote effTy }

effectMult :: Span -> Type -> Type -> Type -> Checker Type
effectMult sp effTy t1 t2 = do
  if isPure t1 then return t2
  else if isPure t2 then return t1
    else
      case effTy of
        -- Nat effects
        TyCon (internalName -> "Nat") ->
          return $ TyInfix TyOpPlus t1 t2

        -- Com (Session), so far just a singleton
        TyCon (internalName -> "Com") ->
          return $ TyCon $ mkId "Session"

        -- Any union-set effects, like IO
        TyCon c | setLike c ->
          case (t1, t2) of
            -- Actual sets, take the union
            (TySet ts1, TySet ts2) ->
              return $ TySet $ nub (ts1 <> ts2)
            _ -> throw $
                  TypeError { errLoc = sp, tyExpected = TySet [TyVar $ mkId "?"], tyActual = t1 }
        _ -> throw $
               UnknownResourceAlgebra { errLoc = sp, errTy = t1, errK = KPromote effTy }

effectUpperBound :: (?globals :: Globals) => Span -> Type -> Type -> Type -> Checker Type
effectUpperBound s t@(TyCon (internalName -> "Nat")) t1 t2 = do
    nvar <- freshTyVarInContextWithBinding (mkId "n") (KPromote t) BoundQ
    -- Unify the two variables into one
    nat1 <- compileNatKindedTypeToCoeffect s t1
    nat2 <- compileNatKindedTypeToCoeffect s t2
    addConstraint (ApproximatedBy s nat1 (CVar nvar) t)
    addConstraint (ApproximatedBy s nat2 (CVar nvar) t)
    return $ TyVar nvar

effectUpperBound _ t@(TyCon (internalName -> "Com")) t1 t2 = do
    return $ TyCon $ mkId "Session"

effectUpperBound s t@(TyCon c) t1 t2 | setLike c = do
    case t1 of
        TySet efs1 ->
            case t2 of
                TySet efs2 ->
                    -- Both sets, take the union
                    return $ TySet (nub (efs1 ++ efs2))
                -- Unit right
                TyCon (internalName -> "Pure") ->
                    return t1
                _ -> throw NoUpperBoundError{ errLoc = s, errTy1 = t1, errTy2 = t2 }
        -- Unift left
        TyCon (internalName -> "Pure") ->
            return t2
        _ ->  throw NoUpperBoundError{ errLoc = s, errTy1 = t1, errTy2 = t2 }

effectUpperBound s effTy t1 t2 =
    throw UnknownResourceAlgebra{ errLoc = s, errTy = t1, errK = KPromote effTy }
