{- Deals with interactions between coeffect resource algebras -}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Flatten
          (mguCoeffectTypes, flattenable) where

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Checker.Monad
import Language.Granule.Utils

mguCoeffectTypes :: (?globals :: Globals)
                 => Span -> Type -> Type -> Checker (Type, (Coeffect -> Coeffect, Coeffect -> Coeffect))
mguCoeffectTypes s t1 t2 = do
  upper <- mguCoeffectTypes' s t1 t2
  case upper of
    Just x -> return x
    -- Cannot unify so form a product
    Nothing -> return
      (TyApp (TyApp (TyCon (mkId "×")) t1) t2,
                  (\x -> CProduct x (COne t2), \x -> CProduct (COne t1) x))

-- Inner definition which does not throw its error, and which operates on just the types
mguCoeffectTypes' :: (?globals :: Globals)
  => Span -> Type -> Type -> Checker (Maybe (Type, (Coeffect -> Coeffect, Coeffect -> Coeffect)))

-- Trivial case
mguCoeffectTypes' s t t' | t == t' = return $ Just (t, (id, id))

-- Both are variables
mguCoeffectTypes' s (TyVar kv1) (TyVar kv2) | kv1 /= kv2 = do
  updateCoeffectType kv1 (KVar kv2)
  return $ Just (TyVar kv2, (id, id))

-- Left-hand side is a poly variable, but Just is concrete
mguCoeffectTypes' s (TyVar kv1) coeffTy2 = do
  updateCoeffectType kv1 (promoteTypeToKind coeffTy2)
  return $ Just (coeffTy2, (id, id))

-- Right-hand side is a poly variable, but Linear is concrete
mguCoeffectTypes' s coeffTy1 (TyVar kv2) = do
  updateCoeffectType kv2 (promoteTypeToKind coeffTy1)
  return $ Just (coeffTy1, (id, id))

-- `Nat` can unify with `Q` to `Q`
mguCoeffectTypes' s (TyCon (internalName -> "Q")) (TyCon (internalName -> "Nat")) =
    return $ Just $ (TyCon $ mkId "Q", (id, inj))
  where inj = coeffectFold $ baseCoeffectFold
                { cNat = \x -> CFloat (fromInteger . toInteger $ x) }

mguCoeffectTypes' s (TyCon (internalName -> "Nat")) (TyCon (internalName -> "Q")) =
    return $ Just $ (TyCon $ mkId "Q", (inj, id))
  where inj = coeffectFold $ baseCoeffectFold
                { cNat = \x -> CFloat (fromInteger . toInteger $ x) }

-- `Nat` can unify with `Ext Nat` to `Ext Nat`
mguCoeffectTypes' s t (TyCon (internalName -> "Nat")) | t == extendedNat =
  return $ Just (extendedNat, (id, id))

mguCoeffectTypes' s (TyCon (internalName -> "Nat")) t | t == extendedNat =
  return $ Just (extendedNat, (id, id))

-- Unifying a product of (t, t') with t yields (t, t') [and the symmetric versions]
mguCoeffectTypes' s coeffTy1@(isProduct -> Just (t1, t2)) coeffTy2 | t1 == coeffTy2 =
  return $ Just (coeffTy1, (id, \x -> CProduct x (COne t2)))

mguCoeffectTypes' s coeffTy1@(isProduct -> Just (t1, t2)) coeffTy2 | t2 == coeffTy2 =
  return $ Just (coeffTy1, (id, \x -> CProduct (COne t1) x))

mguCoeffectTypes' s coeffTy1 coeffTy2@(isProduct -> Just (t1, t2)) | t1 == coeffTy1 =
  return $ Just (coeffTy2, (\x -> CProduct x (COne t2), id))

mguCoeffectTypes' s coeffTy1 coeffTy2@(isProduct -> Just (t1, t2)) | t2 == coeffTy1 =
  return $ Just (coeffTy2, (\x -> CProduct (COne t1) x, id))

-- Unifying with an interval
mguCoeffectTypes' s coeffTy1 coeffTy2@(isInterval -> Just t') | coeffTy1 == t' =
  return $ Just (coeffTy2, (\x -> CInterval x x, id))
mguCoeffectTypes' s coeffTy1@(isInterval -> Just t') coeffTy2 | coeffTy2 == t' =
  return $ Just (coeffTy1, (id, \x -> CInterval x x))

-- Unifying inside an interval (recursive case)

-- Both intervals
mguCoeffectTypes' s (isInterval -> Just t) (isInterval -> Just t') = do
-- See if we can recursively unify inside an interval
  -- This is done in a local type checking context as `mguCoeffectType` can cause unification
  coeffecTyUpper <- mguCoeffectTypes' s t t'
  case coeffecTyUpper of
    Just (upperTy, (inj1, inj2)) ->
      return $ Just (TyApp (TyCon $ mkId "Interval") upperTy, (inj1', inj2'))
            where
              inj1' = coeffectFold baseCoeffectFold{ cInterval = \c1 c2 -> CInterval (inj1 c1) (inj1 c2) }
              inj2' = coeffectFold baseCoeffectFold{ cInterval = \c1 c2 -> CInterval (inj2 c1) (inj2 c2) }
    Nothing -> return Nothing

mguCoeffectTypes' s t (isInterval -> Just t') = do
  -- See if we can recursively unify inside an interval
  -- This is done in a local type checking context as `mguCoeffectType` can cause unification
  coeffecTyUpper <- mguCoeffectTypes' s t t'
  case coeffecTyUpper of
    Just (upperTy, (inj1, inj2)) ->
      return $ Just (TyApp (TyCon $ mkId "Interval") upperTy, (\x -> CInterval (inj1 x) (inj1 x), inj2'))
            where inj2' = coeffectFold baseCoeffectFold{ cInterval = \c1 c2 -> CInterval (inj2 c1) (inj2 c2) }

    Nothing -> return Nothing

mguCoeffectTypes' s (isInterval -> Just t') t = do
  -- See if we can recursively unify inside an interval
  -- This is done in a local type checking context as `mguCoeffectType` can cause unification
  coeffecTyUpper <- mguCoeffectTypes' s t' t
  case coeffecTyUpper of
    Just (upperTy, (inj1, inj2)) ->
      return $ Just (TyApp (TyCon $ mkId "Interval") upperTy, (inj1', \x -> CInterval (inj2 x) (inj2 x)))
            where inj1' = coeffectFold baseCoeffectFold{ cInterval = \c1 c2 -> CInterval (inj1 c1) (inj1 c2) }

    Nothing -> return Nothing

-- No way to unify (outer function will take the product)
mguCoeffectTypes' s coeffTy1 coeffTy2 = return Nothing


-- | Find out whether a coeffect if flattenable, and if so get the operation
-- | used to representing flattening on the grades
flattenable :: (?globals :: Globals)
            => Type -> Type -> Checker (Maybe ((Coeffect -> Coeffect -> Coeffect), Type))
flattenable t1 t2
 | t1 == t2 = case t1 of
    t1 | t1 == extendedNat -> return $ Just (CTimes, t1)

    TyCon (internalName -> "Nat")   -> return $ Just (CTimes, t1)
    TyCon (internalName -> "Level") -> return $ Just (CMeet, t1)

    TyApp (TyCon (internalName -> "Interval")) t ->  flattenable t t

    _ -> return $ Nothing
 | otherwise =
      case (t1, t2) of
        (t1, TyCon (internalName -> "Nat")) | t1 == extendedNat ->
          return $ Just (CTimes, t1)

        (TyCon (internalName -> "Nat"), t2) | t2 == extendedNat ->
          return $ Just (CTimes, t2)

        (t1, t2) -> do
          -- If we have a unification, then use the flattenable
          jK <- mguCoeffectTypes' nullSpan t1 t2
          case jK of
            Just (t, (inj1, inj2)) -> do
              flatM <- flattenable t t
              case flatM of
                Just (op, t) -> return $ Just (\c1 c2 -> op (inj1 c1) (inj2 c2), t)
                Nothing      -> return $ Just (CProduct, TyCon (mkId "×") .@ t1 .@ t2)
            Nothing        -> return $ Just (CProduct, TyCon (mkId "×") .@ t1 .@ t2)

