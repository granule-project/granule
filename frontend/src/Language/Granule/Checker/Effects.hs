{- Deals with effect algebras -}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

-- | Implements effect algebras
module Language.Granule.Checker.Effects where

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Variables

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span

import Language.Granule.Utils

import Data.List (nub, (\\), intersect)

-- Predicate/deconstructor on a type to see if it is
-- application of the free monad construct
isFreeEffectType :: Type -> Maybe (Type, Type)
isFreeEffectType (TyApp (TyApp (TyCon con) labelType) opsType)
 | internalName con == "GradedFree" = Just (labelType, opsType)
isFreeEffectType _ = Nothing

isFreeEffectMember :: Type -> Maybe (Type, Type, Type)
isFreeEffectMember
 (TyApp (TyApp (TyApp (TyCon con) labelType) opsType) grade)
 | internalName con == "Eff" = Just (labelType, opsType, grade)
isFreeEffectMember _ = Nothing

freeEffectMember :: Type -> Type -> [Type] -> Type
freeEffectMember labelType opsType set =
  TyApp (TyApp (TyApp (TyCon $ mkId "Eff") labelType) opsType)
    (TySet Normal set)

isFreeEffectMemberGrade :: Type -> Maybe Type
isFreeEffectMemberGrade
 (TyApp (TyApp (TyApp (TyCon con) _) _) grade)
 | internalName con == "Eff" = Just grade
isFreeEffectMemberGrade (TyCon (internalName -> "Pure")) =
   Just (TySet Normal [])
isFreeEffectMemberGrade _ = Nothing



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
        -- Set effects
        (isSet -> Just (elemTy, polarity)) ->
          case polarity of
            Normal ->
              case eff of
                  -- Is empty set
                  (TySet Normal []) -> return True
                  _                 -> return False
            Opposite -> do
              case eff of
                  -- Is universal set
                  (TySet Opposite elems) -> do
                    constructors <- allDataConstructorNamesForType elemTy
                    return $ all (\uelem -> (TyCon uelem) `elem` elems) constructors
                  _ -> return False
        -- Unknown
        _ -> throw $ UnknownResourceAlgebra { errLoc = s, errTy = eff, errK = effTy }

-- TODO: effTy here seems redundant - I think
-- this could be implemented more generally
handledNormalise :: Span -> Type -> Type -> Type
handledNormalise s effTy efs =
    case efs of
        TyApp (TyCon (internalName -> "Handled")) (TyCon (internalName -> "MayFail")) -> TyCon (mkId "Pure")
        TyApp (TyCon (internalName -> "Handled")) (TyCon (internalName -> "Success")) -> TyCon (mkId "Pure")
        TyApp (TyCon (internalName -> "Handled")) (TySet p efs') -> TySet p (efs' \\ [TyCon (mkId "IOExcept")])
        TyApp (TyCon (internalName -> "Handled")) ef -> handledNormalise s effTy ef
        TyCon (internalName -> "Success") -> TyCon (mkId "Pure")
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
            -- Free graded monad
            (isFreeEffectType -> Just (labelType, opsType)) ->
              case (isFreeEffectMemberGrade eff1, isFreeEffectMemberGrade eff2) of
                (Just (TySet Normal efs1), Just (TySet Normal efs2)) -> return $ all (\ef1 -> ef1 `elem` efs2) efs1
                -- TODO: make more powerful
                _                    -> return False

            -- Any union-set effects, like IO
            (isSet -> Just (elemTy, _)) ->
                case (eff1, eff2) of
                    (TyApp (TyCon (internalName -> "Handled")) efs1, TyApp (TyCon (internalName -> "Handled")) efs2)-> do
                        let efs1' = handledNormalise s effTy eff1
                        let efs2' = handledNormalise s effTy eff2
                        effApproximates s effTy efs1' efs2'
                    --Handled, set
                    (TyApp (TyCon (internalName -> "Handled")) efs1, TySet _ efs2) -> do
                        let efs1' = handledNormalise s effTy eff1
                        effApproximates s effTy efs1' eff2
                    --set, Handled
                    (TySet _ efs1, TyApp (TyCon (internalName -> "Handled")) efs2) -> do
                        let efs2' = handledNormalise s effTy eff1
                        effApproximates s effTy eff1 efs2'
                    -- Both sets
                    (TySet Normal efs1, TySet Normal efs2) ->
                        -- eff1 is a subset of eff2
                        return $ all (\ef1 -> ef1 `elem` efs2) efs1
                    (TySet Opposite efs1, TySet Opposite efs2) ->
                        -- eff1 is a superset of eff2
                        return $ all (\ef2 -> ef2 `elem` efs1) efs2
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
                -- TODO: This type error is not very good. It actual points to a set when sets are not involved
                _ -> throw $ TypeError { errLoc = sp, tyExpected = TySet Normal [TyVar $ mkId "?"], tyActual = t1 }

        (isFreeEffectType -> Just (labelType, opsType)) ->
          case (isFreeEffectMemberGrade t1, isFreeEffectMemberGrade t2) of
            (Just (TySet Normal ef1), Just (TySet Normal ef2)) -> return $ freeEffectMember labelType opsType (nub $ ef1 ++ ef2)
            _ -> return $ TyInfix TyOpTimes t1 t2

        -- Any union-set effects, like IO
        (isSet -> Just (elemTy, polarity)) ->
          case (t1, t2) of
            --Handled, Handled
            (TyApp (TyCon (internalName -> "Handled")) ts1, TyApp (TyCon (internalName -> "Handled")) ts2) -> do
                let ts1' = handledNormalise sp effTy t1
                let ts2' = handledNormalise sp effTy t2
                t <- (effectMult sp effTy ts1' ts2')
                return t
            --Handled, set
            (TyApp (TyCon (internalName -> "Handled")) ts1, TySet _ ts2) -> do
                let ts1' = handledNormalise sp effTy t1
                t <- (effectMult sp effTy ts1' t2) ;
                return t
             --set, Handled
            (TySet _ ts1, TyApp (TyCon (internalName -> "Handled")) ts2) -> do
                let ts2' = handledNormalise sp effTy t2
                t <- (effectMult sp effTy t1 ts2') ;
                return t
            -- Actual sets, take the union
            (TySet p1 ts1, TySet p2 ts2) | p1 == p2 ->
              case p1 of
                Normal   -> return $ TySet p1 (nub (ts1 <> ts2))
                Opposite -> return $ TySet p1 (nub (ts1 `intersect` ts2))
            _ -> throw $
                  TypeError { errLoc = sp, tyExpected = TySet Normal [TyVar $ mkId "?"], tyActual = t1 }
        _ -> do
            -- Unknown operation so just leave this as a syntactic multiplication
            return $ TyInfix TyOpTimes t1 t2
          -- Previously we might through an unknown resource algebra error:
          -- throw $ UnknownResourceAlgebra { errLoc = sp, errTy = t1, errK = effTy }

effectUpperBound :: Span -> Type -> Type -> Type -> Checker Type
-- Upper bound is always idempotent
effectUpperBound s _ t1 t2 | t1 == t2 = return $ t1

effectUpperBound s t@(TyCon (internalName -> "Nat")) t1 t2 = do
    nvar <- freshTyVarInContextWithBinding (mkId "n") t InstanceQ
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

-- Free graded monad
effectUpperBound s (isFreeEffectType -> Just (labelType, opsType)) t1 t2 =
  case (isFreeEffectMemberGrade t1, isFreeEffectMemberGrade t2) of
    (Just (TySet Normal ef1), Just (TySet Normal ef2)) ->
      return $ TySet Normal (nub $ ef1 ++ ef2)
    _ -> throw NoUpperBoundError{ errLoc = s, errTy1 = t1, errTy2 = t2 }

effectUpperBound s (isSet -> Just (elemTy, Normal)) t1 t2 =
    case t1 of
        TySet Normal efs1 ->
            case t2 of
                TySet Normal efs2 ->
                    -- Both sets, take the union
                    return $ TySet Normal (nub (efs1 ++ efs2))
                -- Unit right
                TyCon (internalName -> "Pure") ->
                    return t1
                _ -> throw NoUpperBoundError{ errLoc = s, errTy1 = t1, errTy2 = t2 }
        -- Unit left
        TyCon (internalName -> "Pure") ->
            return t2

        _ ->  throw NoUpperBoundError{ errLoc = s, errTy1 = t1, errTy2 = t2 }

effectUpperBound s (isSet -> Just (elemTy, Opposite)) t1 t2 =
    case t1 of
        -- Opposite sets
        TySet Opposite efs1 ->
            case t2 of
                TySet Opposite efs2 ->
                    -- Both sets, take the union
                    return $ TySet Opposite (nub (efs1 `intersect` efs2))
                -- Unit right
                TyCon (internalName -> "Pure") -> do
                    allConstructorsMatchingForElemTy <- allDataConstructorNamesForType elemTy
                    return (TySet Opposite (map TyCon allConstructorsMatchingForElemTy))

                _ -> throw NoUpperBoundError{ errLoc = s, errTy1 = t1, errTy2 = t2 }
        -- Unit left
        TyCon (internalName -> "Pure") -> do
            allConstructorsMatchingForElemTy <- allDataConstructorNamesForType elemTy
            return (TySet Opposite (map TyCon allConstructorsMatchingForElemTy))

        _ ->  throw NoUpperBoundError{ errLoc = s, errTy1 = t1, errTy2 = t2 }

effectUpperBound s effTy t1 t2 =
    throw UnknownResourceAlgebra{ errLoc = s, errTy = t1, errK = effTy }

-- "Top" element of the effect
effectTop :: Type -> Checker (Maybe Type)
effectTop (TyCon (internalName -> "Nat")) = return $ Nothing
effectTop (TyCon (internalName -> "Com")) = return $ Just $ TyCon $ mkId "Session"
-- Otherwise
-- Based on an effect type, provide its top-element, which for set-like effects
-- like IO can later be aliased to the name of effect type,
-- i.e., a <IO> is an alias for a <{Read, Write, ... }>
effectTop (isSet -> Just (elemTy, Normal)) = do
    -- Compute the full-set of elements based on the the kinds of elements
    -- in the primitives
    allConstructorsMatchingForElemTy <- allDataConstructorNamesForType elemTy
    return (Just $ TySet Normal (map TyCon allConstructorsMatchingForElemTy))

effectTop (isSet -> Just (elemTy, Opposite)) =
    return (Just $ TySet Opposite [])

effectTop (isFreeEffectType -> Just (labelType, opsType)) = do
  allConstructorsMatchingForElemTy <- allDataConstructorNamesForType labelType
  return (Just $ freeEffectMember labelType opsType (map TyCon allConstructorsMatchingForElemTy))

effectTop _ = return Nothing


isPure :: Type -> Bool
isPure (TyCon c) = internalName c == "Pure"
isPure _ = False