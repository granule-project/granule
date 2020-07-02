{- Deals with effect algebras -}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Effects where

import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import qualified Language.Granule.Checker.Primitives as P (setElements, typeConstructors)
import Language.Granule.Checker.Variables

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span

import Language.Granule.Utils

import Data.List (nub, (\\))
import Data.Maybe (mapMaybe)

-- Describe all effect types that are based on a union-emptyset monoid
unionSetLike :: Id -> Bool
unionSetLike (internalName -> "IO") = True
unionSetLike _ = False

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
        -- Any union-set effects, like IO and exceptions
        TyCon (internalName -> "Exception") ->
            case eff of
                TyCon (internalName -> "Success") -> return True
                _ -> return False
        TyCon c | unionSetLike c ->
            case eff of
                (TySet []) -> return True
                _          -> return False
        TyApp op ef ->
            case op of
        --masking operation
                TyCon (internalName -> "Handled") ->
                    isEffUnit s op (handledNormalise s effTy ef)
        --Unknown
                _ -> throw $ UnknownResourceAlgebra { errLoc = s, errTy = eff, errK = KPromote effTy }
        _ -> throw $ UnknownResourceAlgebra { errLoc = s, errTy = eff, errK = KPromote effTy }

handledNormalise :: Span -> Type -> Type -> Type
handledNormalise s effTy efs =
    case effTy of
        (TyApp (TyCon (internalName -> "Handled")) ef) -> handledNormalise s effTy ef
        TyCon (internalName -> "Exception") -> TyCon (mkId "Success")
        TySet efs' -> 
            TySet (efs' \\ [TyCon (mkId "IOExcept")])
        _ -> efs

-- `effApproximates s effTy eff1 eff2` checks whether `eff1 <= eff2` for the `effTy`
-- resource algebra
effApproximates :: (?globals :: Globals) => Span -> Type -> Type -> Type -> Checker Bool
effApproximates s effTy eff1 eff2 =
    -- as 1 <= e for all e
    if isPure eff1 then return True
    else
        case effTy of
            -- Nat case
            TyCon (internalName -> "Nat") -> do
                nat1 <- compileNatKindedTypeToCoeffect s eff1
                nat2 <- compileNatKindedTypeToCoeffect s eff2
                addConstraint (LtEq s nat1 nat2)
                return True
            -- Session singleton case
            TyCon (internalName -> "Com") -> do
                return True
            -- Exceptions
            TyCon (internalName -> "Exception") -> 
                case (eff1, eff2) of
                    (TyCon (internalName -> "Success"),_) ->
                        return True
                    (TyApp (TyCon (internalName -> "Handled")) _, _) ->
                        return True
                    (TyCon (internalName -> "MayFail"),TyCon (internalName -> "MayFail")) ->
                        return True
                    _ -> return False
        -- Any union-set effects, like IO
            TyCon c | unionSetLike c ->
                case (eff1, eff2) of
                    (TyCon (internalName -> "Pure"), _) -> return True
                    (TyApp (TyCon (internalName -> "Handled")) efs1, TyApp (TyCon (internalName -> "Handled")) efs2)-> do
                        let efs1' = handledNormalise s effTy efs1
                        let efs2' = handledNormalise s effTy efs2
                        effApproximates s effTy efs1' efs2'
                    --Handled, set
                    (TyApp (TyCon (internalName -> "Handled")) efs1, TySet efs2) -> do
                        let efs1' = handledNormalise s effTy efs1
                        effApproximates s effTy efs1' eff2
                    --set, Handled
                    (TySet efs1, TyApp (TyCon (internalName -> "Handled")) efs2) -> do
                        let efs2' = handledNormalise s effTy efs2
                        effApproximates s effTy eff1 efs2'
                    -- Actual sets, take the union
                    (TySet efs1, TySet efs2) ->
                        -- eff1 is a subset of eff2
                        return $ all (\ef1 -> ef1 `elem` efs2) efs1
                    _ -> return False
                    -- Unknown effect resource algebra
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

        TyCon (internalName -> "Exception") ->
            case t1 of
                TyApp (TyCon (internalName -> "Handled")) _ -> 
                    case t2 of
                        TyCon (internalName -> "MayFail") ->
                            return $ TyCon $ mkId "MayFail"
                        _ ->
                            return $ TyCon $ mkId "Success"
                TyCon (internalName -> "Success") ->
                    case t2 of
                    TyCon (internalName -> "MayFail") ->
                        return $ TyCon $ mkId "MayFail"
                    _ ->
                        return $ TyCon $ mkId "Success"
                TyCon (internalName -> "MayFail") ->
                    return $ TyCon $ mkId "MayFail"
                _ -> throw $ TypeError { errLoc = sp, tyExpected = TySet [TyVar $ mkId "?"], tyActual = t1 }

        -- Any union-set effects, like IO
        TyCon c | unionSetLike c ->
          case (t1, t2) of
            --Handled, Handled
            (TyApp (TyCon (internalName -> "Handled")) ts1, TyApp (TyCon (internalName -> "Handled")) ts2) -> do
                let ts1' = handledNormalise sp effTy ts1
                let ts2' = handledNormalise sp effTy ts2 
                t <- (effectMult sp effTy ts1' ts2')
                return t
            --Handled, set
            (TyApp (TyCon (internalName -> "Handled")) ts1, TySet ts2) -> do
                let ts1' = handledNormalise sp effTy ts1
                t <- (effectMult sp effTy ts1' t2) ; 
                return t
             --set, Handled
            (TySet ts1, TyApp (TyCon (internalName -> "Handled")) ts2) -> do
                let ts2' = handledNormalise sp effTy ts2 
                t <- (effectMult sp effTy t1 ts2') ;
                return t
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

effectUpperBound s t@(TyCon (internalName -> "Exception")) t1 t2 = do
    case (t1, t2) of
        (TyCon (internalName -> "Success"),TyCon (internalName -> "Success")) ->
            return t1
        (TyCon (internalName -> "Success"),TyCon (internalName -> "MayFail")) ->
            return t2
        (TyCon (internalName -> "MayFail"),TyCon (internalName -> "Success")) ->
            return t1
        (TyCon (internalName -> "MayFail"),TyCon (internalName -> "MayFail")) ->
            return t1
        (TyCon (internalName -> "Pure"), _) ->
            return t1
        (_, TyCon (internalName -> "Pure")) ->
            return t2
        _ -> throw NoUpperBoundError{ errLoc = s, errTy1 = t1, errTy2 = t2 }

effectUpperBound s t@(TyCon c) t1 t2 | unionSetLike c = do
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

-- "Top" element of the effect
effectTop :: Type -> Maybe Type
effectTop (TyCon (internalName -> "Nat")) = Nothing
effectTop (TyCon (internalName -> "Com")) = Just $ TyCon $ mkId "Session"
-- Otherwise
-- Based on an effect type, provide its top-element, which for set-like effects
-- like IO can later be aliased to the name of effect type,
-- i.e., a <IO> is an alias for a <{Read, Write, ... }>
effectTop t = do
    -- Compute the full-set of elements based on the the kinds of elements
    -- in the primitives
    elemKind <- lookup t (map swap P.setElements)
    return (TySet (map TyCon (allConstructorsMatchingElemKind elemKind)))
  where
    swap (a, b) = (b, a)
    -- find all elements of the matching element type
    allConstructorsMatchingElemKind elemKind = mapMaybe (go elemKind) P.typeConstructors
    go elemKind (con, (k, _, _)) =
        if k == elemKind then Just con else Nothing

isPure :: Type -> Bool
isPure (TyCon c) = internalName c == "Pure"
isPure _ = False