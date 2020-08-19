{- Deals with interactions between coeffect resource algebras -}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Flatten
          (mguCoeffectTypes, flattenable) where

import Control.Monad.State.Strict

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Utils

cProduct :: Type -> Type -> Type
cProduct x y = TyApp (TyApp (TyCon (mkId "×")) x) y

mguCoeffectTypes :: (?globals :: Globals)
                 => Span -> Type -> Type -> Checker (Type, Substitution, (Type -> Type, Type -> Type))
mguCoeffectTypes s t1 t2 = do
  upper <- mguCoeffectTypes' s t1 t2
  case upper of
    Just x -> return x
    -- Cannot unify so form a product
    Nothing -> return
      (TyApp (TyApp (TyCon (mkId "×")) t1) t2, [],
                  (\x -> cProduct x (TyInt 1), \x -> cProduct (TyInt 1) x))

-- Inner definition which does not throw its error, and which operates on just the types
mguCoeffectTypes' :: (?globals :: Globals)
  => Span -> Type -> Type -> Checker (Maybe (Type, Substitution, (Type -> Type, Type -> Type)))

-- Trivial case
mguCoeffectTypes' s t t' | t == t' = return $ Just (t, [], (id, id))

-- Both are variables
mguCoeffectTypes' s (TyVar kv1) (TyVar kv2) | kv1 /= kv2 = do
  st <- get
  case (lookup kv1 (tyVarContext st), lookup kv2 (tyVarContext st))  of
    (Nothing, _) -> throw $ UnboundVariableError s kv1
    (_, Nothing) -> throw $ UnboundVariableError s kv2
    (Just (KCoeffect, _), Just (KCoeffect, InstanceQ)) -> do
      updateCoeffectType kv2 (KVar kv1)
      return $ Just (TyVar kv1, [(kv2, SubstK $ KVar kv1)], (id, id))

    (Just (KCoeffect, InstanceQ), Just (KCoeffect, _)) -> do
      updateCoeffectType kv1 (KVar kv2)
      return $ Just (TyVar kv2, [(kv1, SubstK $ KVar kv2)], (id, id))

    (Just (KCoeffect, ForallQ), Just (KCoeffect, ForallQ)) -> do
      throw $ UnificationFail s kv2 (TyVar kv1) KCoeffect False

    (Just (KCoeffect, _), Just (k, _)) -> throw $ KindMismatch s Nothing KCoeffect k

    (Just (KEffect, _), Just (KEffect, InstanceQ)) -> do
      updateCoeffectType kv2 (KVar kv1)
      return $ Just (TyVar kv1, [(kv2, SubstK $ KVar kv1)], (id, id))

    (Just (KEffect, InstanceQ), Just (KEffect, _)) -> do
      updateCoeffectType kv1 (KVar kv2)
      return $ Just (TyVar kv2, [(kv1, SubstK $ KVar kv2)], (id, id))

    (Just (KEffect, ForallQ), Just (KEffect, ForallQ)) -> do
      throw $ UnificationFail s kv2 (TyVar kv1) KEffect False

    (Just (KEffect, _), Just (k, _)) -> throw $ KindMismatch s Nothing KEffect k
    (Just (k, _), Just (_, _))       -> throw $ KindMismatch s Nothing KCoeffect k



-- Left-hand side is a poly variable, but Just is concrete
mguCoeffectTypes' s (TyVar kv1) coeffTy2 = do
  st <- get
  case lookup kv1 (tyVarContext st) of
    Nothing -> throw $ UnboundVariableError s kv1
    Just (k, ForallQ) ->
      throw $ UnificationFail s kv1 coeffTy2 k True
    Just (k, _) -> do -- InstanceQ or BoundQ
      updateCoeffectType kv1 (promoteTypeToKind coeffTy2)
      return $ Just (coeffTy2, [(kv1, SubstT coeffTy2)], (id, id))

-- Right-hand side is a poly variable, but Linear is concrete
mguCoeffectTypes' s coeffTy1 (TyVar kv2) = do

  st <- get
  case lookup kv2 (tyVarContext st) of
    Nothing -> throw $ UnboundVariableError s kv2
    Just (k, ForallQ) ->
      throw $ UnificationFail s kv2 coeffTy1 k True
    Just (k, _) -> do -- InstanceQ or BoundQ
      updateCoeffectType kv2 (promoteTypeToKind coeffTy1)
      return $ Just (coeffTy1, [(kv2, SubstT coeffTy1)], (id, id))

-- `Nat` can unify with `Q` to `Q`
mguCoeffectTypes' s (TyCon (internalName -> "Q")) (TyCon (internalName -> "Nat")) =
    return $ Just $ (TyCon $ mkId "Q", [], (id, inj))
  where inj = typeFold $ baseTypeFold
                { tfTyInt = \x -> return $ TyFloat (fromInteger . toInteger $ x) }

mguCoeffectTypes' s (TyCon (internalName -> "Nat")) (TyCon (internalName -> "Q")) =
    return $ Just $ (TyCon $ mkId "Q", [], (inj, id))
  where inj = typeFold $ baseTypeFold
                { tfTyInt = \x -> return $ TyFloat (fromInteger . toInteger $ x) }

-- `Nat` can unify with `Ext Nat` to `Ext Nat`
mguCoeffectTypes' s t (TyCon (internalName -> "Nat")) | t == extendedNat =
  return $ Just (extendedNat, [], (id, id))

mguCoeffectTypes' s (TyCon (internalName -> "Nat")) t | t == extendedNat =
  return $ Just (extendedNat, [], (id, id))

-- Unifying a product of (t, t') with t yields (t, t') [and the symmetric versions]
mguCoeffectTypes' s coeffTy1@(isProduct -> Just (t1, t2)) coeffTy2 | t1 == coeffTy2 =
  return $ Just (coeffTy1, [], (id, \x -> cProduct x (TyInt 1)))

mguCoeffectTypes' s coeffTy1@(isProduct -> Just (t1, t2)) coeffTy2 | t2 == coeffTy2 =
  return $ Just (coeffTy1, [], (id, \x -> cProduct (TyInt 1) x))

mguCoeffectTypes' s coeffTy1 coeffTy2@(isProduct -> Just (t1, t2)) | t1 == coeffTy1 =
  return $ Just (coeffTy2, [], (\x -> cProduct x (TyInt 1), id))

mguCoeffectTypes' s coeffTy1 coeffTy2@(isProduct -> Just (t1, t2)) | t2 == coeffTy1 =
  return $ Just (coeffTy2, [], (\x -> cProduct (TyInt 1) x, id))

-- Unifying with an interval
mguCoeffectTypes' s coeffTy1 coeffTy2@(isInterval -> Just t') | coeffTy1 == t' =
  return $ Just (coeffTy2, [], (\x -> TyInfix TyOpInterval x x, id))
mguCoeffectTypes' s coeffTy1@(isInterval -> Just t') coeffTy2 | coeffTy2 == t' =
  return $ Just (coeffTy1, [], (id, \x -> TyInfix TyOpInterval x x))

-- Unifying inside an interval (recursive case)

-- Both intervals
mguCoeffectTypes' s (isInterval -> Just t) (isInterval -> Just t') = do
-- See if we can recursively unify inside an interval
  -- This is done in a local type checking context as `mguCoeffectType` can cause unification
  coeffecTyUpper <- mguCoeffectTypes' s t t'
  case coeffecTyUpper of
    Just (upperTy, subst, (inj1, inj2)) ->
      return $ Just (TyApp (TyCon $ mkId "Interval") upperTy, subst, (inj1', inj2'))
            where
              inj1' = typeFold baseTypeFold { tfTyInfix = \op c1 c2 -> return $ case op of TyOpInterval -> TyInfix op (inj1 c1) (inj1 c2); _ -> TyInfix op c1 c2 }
              inj2' = typeFold baseTypeFold { tfTyInfix = \op c1 c2 -> return $ case op of TyOpInterval -> TyInfix op (inj2 c1) (inj2 c2); _ -> TyInfix op c1 c2 }
    Nothing -> return Nothing

mguCoeffectTypes' s t (isInterval -> Just t') = do
  -- See if we can recursively unify inside an interval
  -- This is done in a local type checking context as `mguCoeffectType` can cause unification
  coeffecTyUpper <- mguCoeffectTypes' s t t'
  case coeffecTyUpper of
    Just (upperTy, subst, (inj1, inj2)) ->
      return $ Just (TyApp (TyCon $ mkId "Interval") upperTy, subst, (\x -> TyInfix TyOpInterval (inj1 x) (inj1 x), inj2'))
            where inj2' = typeFold baseTypeFold { tfTyInfix = \op c1 c2 -> return $ case op of TyOpInterval -> TyInfix op (inj2 c1) (inj2 c2); _ -> TyInfix op c1 c2 }

    Nothing -> return Nothing

mguCoeffectTypes' s (isInterval -> Just t') t = do
  -- See if we can recursively unify inside an interval
  -- This is done in a local type checking context as `mguCoeffectType` can cause unification
  coeffecTyUpper <- mguCoeffectTypes' s t' t
  case coeffecTyUpper of
    Just (upperTy, subst, (inj1, inj2)) ->
      return $ Just (TyApp (TyCon $ mkId "Interval") upperTy, subst, (inj1', \x -> TyInfix TyOpInterval (inj2 x) (inj2 x)))
            where inj1' = typeFold baseTypeFold { tfTyInfix = \op c1 c2 -> return $ case op of TyOpInterval -> TyInfix op (inj1 c1) (inj1 c2); _ -> TyInfix op c1 c2 }

    Nothing -> return Nothing

-- No way to unify (outer function will take the product)
mguCoeffectTypes' s coeffTy1 coeffTy2 = return Nothing


-- | Find out whether a coeffect if flattenable, and if so get the operation
-- | used to representing flattening on the grades
flattenable :: (?globals :: Globals)
            => Type -> Type -> Checker (Maybe (Type -> Type -> Type, Substitution, Type))
flattenable t1 t2
 | t1 == t2 = case t1 of
    t1 | t1 == extendedNat -> return $ Just (TyInfix TyOpTimes, [], t1)

    TyCon (internalName -> "Nat")   -> return $ Just (TyInfix TyOpTimes, [], t1)
    TyCon (internalName -> "Level") -> return $ Just (TyInfix TyOpMeet, [], t1)

    TyApp (TyCon (internalName -> "Interval")) t ->  flattenable t t

    _ -> return $ Nothing
 | otherwise =
      case (t1, t2) of
        (t1, TyCon (internalName -> "Nat")) | t1 == extendedNat ->
          return $ Just (TyInfix TyOpTimes, [], t1)

        (TyCon (internalName -> "Nat"), t2) | t2 == extendedNat ->
          return $ Just (TyInfix TyOpTimes, [], t2)

        (t1, t2) -> do
          -- If we have a unification, then use the flattenable
          jK <- mguCoeffectTypes' nullSpan t1 t2
          case jK of
            Just (t, subst, (inj1, inj2)) -> do
              flatM <- flattenable t t
              case flatM of
                Just (op, subst', t) ->
                  return $ Just (\c1 c2 -> op (inj1 c1) (inj2 c2), subst', t)
                Nothing      -> return $ Just (cProduct, subst, TyCon (mkId "×") .@ t1 .@ t2)
            Nothing        -> return $ Just (cProduct, [], TyCon (mkId "×") .@ t1 .@ t2)

