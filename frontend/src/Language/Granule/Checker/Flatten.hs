{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -fmax-pmcheck-iterations=30000000 #-}

-- | Deals with interactions between coeffect resource algebras
module Language.Granule.Checker.Flatten
          (mguCoeffectTypes, flattenable, Injections) where

import Data.Functor.Identity (runIdentity)
import Control.Monad.State.Strict

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
-- import Language.Granule.Syntax.Pretty
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Utils

type Injections = (Coeffect -> Coeffect, Coeffect -> Coeffect)

cProduct :: Type -> Type -> Type
cProduct x y = TyApp (TyApp (TyCon (mkId ",,")) x) y


-- Compute the most general unification between two coeffect types
-- which produces their unification, a substitution, and a pair of injections
-- for terms of the previous types. i.e.,
--  if `mguCoeffectTypes t1 t2` yields type `t3` and injections `(i1, i2)`
--  then if `r1 : t1` and `r2 : t2` then `i1 r1 : t3` and `i2 t2 : t3`.

mguCoeffectTypes :: (?globals :: Globals)
                 => Span -> Type -> Type -> Checker (Type, Substitution, Injections)
mguCoeffectTypes s t1 t2 = do
  upper <- mguCoeffectTypes' s t1 t2
  case upper of
    Just x -> return x
    -- Cannot unify so form a product
    Nothing -> return
      (TyApp (TyApp (TyCon (mkId ",,")) t1) t2, [],
                  (\x -> cProduct x (TyGrade (Just t2) 1), \x -> cProduct (TyGrade (Just t1) 1) x))

-- Inner definition which does not throw its error, and which operates on just the types
mguCoeffectTypes' :: (?globals :: Globals)
  => Span -> Type -> Type -> Checker (Maybe (Type, Substitution, (Coeffect -> Coeffect, Coeffect -> Coeffect)))

-- Trivial case
mguCoeffectTypes' s t t' | t == t' = return $ Just (t, [], (id, id))

-- Both are variables
mguCoeffectTypes' s (TyVar kv1) (TyVar kv2) | kv1 /= kv2 = do
  st <- get
  case (lookup kv1 (tyVarContext st), lookup kv2 (tyVarContext st))  of
    (Nothing, _) -> throw $ UnboundVariableError s kv1
    (_, Nothing) -> throw $ UnboundVariableError s kv2
    (Just (TyCon (internalName -> "Coeffect"), _), Just (TyCon (internalName -> "Coeffect"), InstanceQ)) -> do
      updateCoeffectType kv2 (TyVar kv1)
      return $ Just (TyVar kv1, [(kv2, SubstT $ TyVar kv1)], (id, id))

    (Just (TyCon (internalName -> "Coeffect"), InstanceQ), Just (TyCon (internalName -> "Coeffect"), _)) -> do
      updateCoeffectType kv1 (TyVar kv2)
      return $ Just (TyVar kv2, [(kv1, SubstT $ TyVar kv2)], (id, id))

    (Just (TyCon (internalName -> "Coeffect"), ForallQ), Just (TyCon (internalName -> "Coeffect"), ForallQ)) ->
      throw $ UnificationFail s kv2 (TyVar kv1) (TyCon $ mkId "Coeffect") False

    (Just (TyCon (internalName -> "Coeffect"), _), Just (k, _)) ->
      throw $ KindMismatch s Nothing (TyCon (mkId "Coeffect")) k

    (Just (k, _), Just (_, _)) ->
      throw $ KindMismatch s Nothing (TyCon (mkId "Coeffect")) k


-- Left-hand side is a poly variable, but Just is concrete
mguCoeffectTypes' s (TyVar kv1) coeffTy2 = do
  st <- get

  case lookup kv1 (tyVarContext st) of
    Nothing -> throw $ UnboundVariableError s kv1

    -- Cannot unify if the type variable is univrssal
    Just (k, ForallQ) ->
      throw $ UnificationFail s kv1 coeffTy2 k True

    -- Can unify if the type variable is a unification var
    Just (k, _) -> do -- InstanceQ or BoundQ
      updateCoeffectType kv1 coeffTy2
      return $ Just (coeffTy2, [(kv1, SubstT coeffTy2)], (id, id))

-- Right-hand side is a poly variable, but Linear is concrete
mguCoeffectTypes' s coeffTy1 (TyVar kv2) = do
  mguCoeffectTypes' s (TyVar kv2) coeffTy1

-- Ext cases
-- unify (Ext t) (Ext t') = Ext (unify t t')
mguCoeffectTypes' s (isExt -> Just t) (isExt -> Just t') = do
  coeffecTyUpper <- mguCoeffectTypes' s t t'
  case coeffecTyUpper of
    Just (upperTy, subst, (inj1, inj2)) -> do
      return $ Just (TyApp (TyCon $ mkId "Ext") upperTy, subst, (inj1, inj2))
    Nothing -> return Nothing

-- unify (Ext t) t' = Ext (unify t t')
mguCoeffectTypes' s (isExt -> Just t) t' = do
  -- liftIO $ putStrLn $ "unify (Ext " <> pretty t <> ") with " <> pretty t'
  coeffecTyUpper <- mguCoeffectTypes' s t t'
  case coeffecTyUpper of
    Just (upperTy, subst, (inj1, inj2)) -> do
      return $ Just (TyApp (TyCon $ mkId "Ext") upperTy, subst, (inj1, inj2))
    Nothing -> return Nothing

-- unify t (Ext t') = Ext (unify t t')
mguCoeffectTypes' s t (isExt -> Just t') = do
  -- liftIO $ putStrLn $ "unify " <> pretty t <> " with (Ext " <> pretty t' <> ")"
  coeffecTyUpper <- mguCoeffectTypes' s t t'
  case coeffecTyUpper of
    Just (upperTy, subst, (inj1, inj2)) -> do
      return $ Just (TyApp (TyCon $ mkId "Ext") upperTy, subst, (inj1, inj2))
    Nothing -> return Nothing

-- `Nat` can unify with `Q` to `Q`
mguCoeffectTypes' s (TyCon (internalName -> "Q")) (TyCon (internalName -> "Nat")) =
    return $ Just $ (TyCon $ mkId "Q", [], (id, inj))
  where inj =  runIdentity . typeFoldM baseTypeFold
                { tfTyInt = \x -> return $ TyRational (fromInteger . toInteger $ x) }

mguCoeffectTypes' s (TyCon (internalName -> "Nat")) (TyCon (internalName -> "Q")) =
    return $ Just $ (TyCon $ mkId "Q", [], (inj, id))
  where inj = runIdentity . typeFoldM baseTypeFold
                { tfTyInt = \x -> return $ TyRational (fromInteger . toInteger $ x) }

-- `Nat` can unify with `Ext Nat` to `Ext Nat`
mguCoeffectTypes' s t (TyCon (internalName -> "Nat")) | t == extendedNat =
  return $ Just (extendedNat, [], (id, id))

mguCoeffectTypes' s (TyCon (internalName -> "Nat")) t | t == extendedNat =
  return $ Just (extendedNat, [], (id, id))

-- Unifying a product of (t, t') with t yields (t, t') [and the symmetric versions]
mguCoeffectTypes' s coeffTy1@(isProduct -> Just (t1, t2)) coeffTy2 | t1 == coeffTy2 =
  return $ Just (coeffTy1, [], (id, \x -> cProduct x (TyGrade (Just t2) 1)))

mguCoeffectTypes' s coeffTy1@(isProduct -> Just (t1, t2)) coeffTy2 | t2 == coeffTy2 =
  return $ Just (coeffTy1, [], (id, \x -> cProduct (TyGrade (Just t1) 1) x))

mguCoeffectTypes' s coeffTy1 coeffTy2@(isProduct -> Just (t1, t2)) | t1 == coeffTy1 =
  return $ Just (coeffTy2, [], (\x -> cProduct x (TyGrade (Just t2) 1), id))

mguCoeffectTypes' s coeffTy1 coeffTy2@(isProduct -> Just (t1, t2)) | t2 == coeffTy1 =
  return $ Just (coeffTy2, [], (\x -> cProduct (TyGrade (Just t1) 1) x, id))

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
    Just (upperTy, subst, (inj1, inj2)) -> do
      return $ Just (TyApp (TyCon $ mkId "Interval") upperTy, subst, (inj1', inj2'))
            where
              inj1' = runIdentity . typeFoldM baseTypeFold { tfTyInfix = \op c1 c2 -> return $ case op of TyOpInterval -> TyInfix op (inj1 c1) (inj1 c2); _ -> TyInfix op c1 c2 }
              inj2' = runIdentity . typeFoldM baseTypeFold { tfTyInfix = \op c1 c2 -> return $ case op of TyOpInterval -> TyInfix op (inj2 c1) (inj2 c2); _ -> TyInfix op c1 c2 }
    Nothing -> return Nothing

mguCoeffectTypes' s t (isInterval -> Just t') = do
  -- See if we can recursively unify inside an interval
  -- This is done in a local type checking context as `mguCoeffectType` can cause unification
  coeffecTyUpper <- mguCoeffectTypes' s t t'
  case coeffecTyUpper of
    Just (upperTy, subst, (inj1, inj2)) ->
      return $ Just (TyApp (TyCon $ mkId "Interval") upperTy, subst, (\x -> TyInfix TyOpInterval (inj1 x) (inj1 x), inj2'))
            where inj2' = runIdentity . typeFoldM baseTypeFold { tfTyInfix = \op c1 c2 -> return $ case op of TyOpInterval -> TyInfix op (inj2 c1) (inj2 c2); _ -> TyInfix op c1 c2 }

    Nothing -> return Nothing

mguCoeffectTypes' s (isInterval -> Just t') t = do
  -- See if we can recursively unify inside an interval
  -- This is done in a local type checking context as `mguCoeffectType` can cause unification
  coeffecTyUpper <- mguCoeffectTypes' s t' t
  case coeffecTyUpper of
    Just (upperTy, subst, (inj1, inj2)) ->
      return $ Just (TyApp (TyCon $ mkId "Interval") upperTy, subst, (inj1', \x -> TyInfix TyOpInterval (inj2 x) (inj2 x)))
            where inj1' = runIdentity . typeFoldM baseTypeFold { tfTyInfix = \op c1 c2 -> return $ case op of TyOpInterval -> TyInfix op (inj1 c1) (inj1 c2); _ -> TyInfix op c1 c2 }

    Nothing -> return Nothing


-- No way to unify (outer function will take the product)
mguCoeffectTypes' s coeffTy1 coeffTy2 = return Nothing


-- | Find out whether a coeffect if flattenable, and if so get the operation
-- | used to represent flattening on the grades
flattenable :: (?globals :: Globals)
            => Type -> Type -> Checker (Maybe ((Coeffect -> Coeffect -> Coeffect), Substitution, Type))
flattenable t1 t2
 | t1 == t2 = case t1 of
    t1 | t1 == extendedNat -> return $ Just (TyInfix TyOpTimes, [], t1)

    TyCon (internalName -> "Nat")   -> return $ Just (TyInfix TyOpTimes, [], t1)
    TyCon (internalName -> "Level") -> return $ Just (TyInfix TyOpMeet, [], t1)

    TyApp (TyCon (internalName -> "Interval")) t ->  flattenable t t

    -- Sets can use multiply to fold two levels
    (isSet -> Just (elemType, polarity)) -> return $ Just (TyInfix TyOpTimes, [], t1)

    _ -> return $ Nothing
 | otherwise =
      case (t1, t2) of
        (isInterval -> Just t, TyCon (internalName -> "LNL")) | t == extendedNat ->
          return $ Just (TyInfix TyOpTimes, [], TyApp (TyCon $ mkId "Interval") extendedNat)

        (TyCon (internalName -> "LNL"), isInterval -> Just t) | t == extendedNat ->
          return $ Just (TyInfix TyOpTimes, [], TyApp (TyCon $ mkId "Interval") extendedNat)

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
                Nothing      -> return $ Just (cProduct, subst, TyCon (mkId ",,") .@ t1 .@ t2)
            Nothing        -> return $ Just (cProduct, [], TyCon (mkId ",,") .@ t1 .@ t2)

