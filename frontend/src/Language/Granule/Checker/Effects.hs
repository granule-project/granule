{- Deals with effect algebras -}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

-- | Implements effect algebras
module Language.Granule.Checker.Effects where

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import qualified Language.Granule.Checker.Primitives as P (typeConstructors)
import Language.Granule.Checker.Variables

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span

import Language.Granule.Utils

import Data.List (nub, (\\))
import Data.Maybe (mapMaybe)

-- `isEffUnit sp effTy eff` checks whether `eff` of effect type `effTy`
-- is equal to the unit element of the algebra.
isEffUnit :: Span -> Type -> Type -> Checker Bool
isEffUnit s effTy eff =
    case effTy of
        -- Nat case
        TyCon (internalName -> "Nat") -> do
            addConstraint (Eq s (TyInt 0) eff (TyCon $ mkId "Nat"))
            return True
        -- Session singleton case
        TyCon (internalName -> "Com") -> do
            return True
        TyCon (internalName -> "Exception") ->
            case eff of
                TyCon (internalName -> "Success") -> return True
                _ -> return False
        -- Any union-set effects, like IO
        (isSet -> Just elemTy) ->
            case eff of
                (TySet []) -> return True
                _          -> return False
        -- Unknown
        _ -> throw $ UnknownResourceAlgebra { errLoc = s, errTy = eff, errK = effTy }

-- TODO: effTy here seems redundant - I think
-- this could be implemented more generally
handledNormalise :: Span -> Type -> Type -> Type
handledNormalise s effTy efs =
    case efs of
        TyApp (TyCon (internalName -> "Handled")) (TyCon (internalName -> "MayFail")) -> TyCon (mkId "Pure")
        TyApp (TyCon (internalName -> "Handled")) (TyCon (internalName -> "Success")) -> TyCon (mkId "Pure")
        TyApp (TyCon (internalName -> "Handled")) ef -> handledNormalise s effTy ef
        TyCon (internalName -> "Success") -> TyCon (mkId "Pure")
        TySet efs' ->
            TySet (efs' \\ [TyCon (mkId "IOExcept")])
        _ -> efs

-- `effApproximates s effTy eff1 eff2` checks whether `eff1 <= eff2` for the `effTy`
-- resource algebra
effApproximates :: Span -> Type -> Type -> Type -> Checker Bool
effApproximates s effTy eff1 eff2 =
    -- as 1 <= e for all e
    if isPure eff1 then return True
    else
        case effTy of
            -- Nat case
            TyCon (internalName -> "Nat") -> do
                addConstraint (LtEq s eff1 eff2)
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
            (isSet -> Just elemTy) ->
                case (eff1, eff2) of
                    (TyApp (TyCon (internalName -> "Handled")) efs1, TyApp (TyCon (internalName -> "Handled")) efs2)-> do
                        let efs1' = handledNormalise s effTy eff1
                        let efs2' = handledNormalise s effTy eff2
                        effApproximates s effTy efs1' efs2'
                    --Handled, set
                    (TyApp (TyCon (internalName -> "Handled")) efs1, TySet efs2) -> do
                        let efs1' = handledNormalise s effTy eff1
                        effApproximates s effTy efs1' eff2
                    --set, Handled
                    (TySet efs1, TyApp (TyCon (internalName -> "Handled")) efs2) -> do
                        let efs2' = handledNormalise s effTy eff1
                        effApproximates s effTy eff1 efs2'
                    -- Actual sets, take the union
                    (TySet efs1, TySet efs2) ->
                        -- eff1 is a subset of eff2
                        return $ all (\ef1 -> ef1 `elem` efs2) efs1
                    _ -> return False
            -- Unknown effect resource algebra
            _ -> throw $ UnknownResourceAlgebra { errLoc = s, errTy = eff1, errK = effTy }

effectMult :: (?globals :: Globals) => Span -> Type -> Type -> Type -> Checker Type
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
                --derived property Handled f * e = e
                TyApp (TyCon (internalName -> "Handled")) _ ->
                    return t2
                TyCon (internalName -> "Success") ->
                    return t2
                TyCon (internalName -> "MayFail") ->
                    return $ TyCon $ mkId "MayFail"
                _ -> throw $ TypeError { errLoc = sp, tyExpected = TySet [TyVar $ mkId "?"], tyActual = t1 }

        -- Any union-set effects, like IO
        (isSet -> Just elemTy) ->
          case (t1, t2) of
            --Handled, Handled
            (TyApp (TyCon (internalName -> "Handled")) ts1, TyApp (TyCon (internalName -> "Handled")) ts2) -> do
                let ts1' = handledNormalise sp effTy t1
                let ts2' = handledNormalise sp effTy t2
                t <- (effectMult sp effTy ts1' ts2')
                return t
            --Handled, set
            (TyApp (TyCon (internalName -> "Handled")) ts1, TySet ts2) -> do
                let ts1' = handledNormalise sp effTy t1
                t <- (effectMult sp effTy ts1' t2) ;
                return t
             --set, Handled
            (TySet ts1, TyApp (TyCon (internalName -> "Handled")) ts2) -> do
                let ts2' = handledNormalise sp effTy t2
                t <- (effectMult sp effTy t1 ts2') ;
                return t
            -- Actual sets, take the union
            (TySet ts1, TySet ts2) ->
              return $ TySet $ nub (ts1 <> ts2)
            _ -> throw $
                  TypeError { errLoc = sp, tyExpected = TySet [TyVar $ mkId "?"], tyActual = t1 }
        _ -> do
          throw $ UnknownResourceAlgebra { errLoc = sp, errTy = t1, errK = effTy }

effectUpperBound :: Span -> Type -> Type -> Type -> Checker Type
effectUpperBound s t@(TyCon (internalName -> "Nat")) t1 t2 = do
    nvar <- freshTyVarInContextWithBinding (mkId "n") t BoundQ
    -- Unify the two variables into one
    addConstraint (ApproximatedBy s t1 (TyVar nvar) t)
    addConstraint (ApproximatedBy s t2 (TyVar nvar) t)
    return $ TyVar nvar

effectUpperBound _ t@(TyCon (internalName -> "Com")) t1 t2 = do
    return $ TyCon $ mkId "Session"

effectUpperBound s t@(TyCon (internalName -> "Exception")) t1 t2 = do
    let t1' = handledNormalise s t t1
    let t2' = handledNormalise s t t2
    case (t1', t2') of
        (TyCon (internalName -> "Success"),TyCon (internalName -> "Success")) ->
            return t1'
        (TyCon (internalName -> "MayFail"),_) ->
            return t1'
        (_,TyCon (internalName -> "MayFail")) ->
            return t2'
        (TyCon (internalName -> "Pure"), _) ->
            return t1'
        (_, TyCon (internalName -> "Pure")) ->
            return t2'
        _ -> throw NoUpperBoundError{ errLoc = s, errTy1 = t1', errTy2 = t2' }

effectUpperBound s (isSet -> Just elemTy) t1 t2 =
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
    throw UnknownResourceAlgebra{ errLoc = s, errTy = t1, errK = effTy }

-- "Top" element of the effect
effectTop :: Type -> Maybe Type
effectTop (TyCon (internalName -> "Nat")) = Nothing
effectTop (TyCon (internalName -> "Com")) = Just $ TyCon $ mkId "Session"
-- Otherwise
-- Based on an effect type, provide its top-element, which for set-like effects
-- like IO can later be aliased to the name of effect type,
-- i.e., a <IO> is an alias for a <{Read, Write, ... }>
effectTop (isSet -> Just elemTy) =
    -- Compute the full-set of elements based on the the kinds of elements
    -- in the primitives
    return (TySet (map TyCon allConstructorsMatchingElemKind))
  where
    -- find all elements of the matching element type
    allConstructorsMatchingElemKind :: [Id]
    allConstructorsMatchingElemKind = mapMaybe go P.typeConstructors

    go :: (Id, (Type, a, Bool)) -> Maybe Id
    go (con, (k, _, _)) = if k == elemTy then Just con else Nothing

effectTop _ = Nothing

isPure :: Type -> Bool
isPure (TyCon c) = internalName c == "Pure"
isPure _ = False