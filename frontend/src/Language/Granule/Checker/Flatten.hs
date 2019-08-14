{- Deals with interactions between coeffect resource algebras -}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Flatten where

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type

-- | Some coeffect types can be joined (have a least-upper bound). This
-- | function computes the join if it exists.
joinCoeffectTypes :: Type -> Type -> Maybe Type
joinCoeffectTypes t1 t2 = case (t1, t2) of
    -- Equal things unify to the same thing
    (t, t') | t == t' -> Just t

    -- `Nat` can unify with `Q` to `Q`
    (TyCon (internalName -> "Q"), TyCon (internalName -> "Nat")) ->
        Just $ TyCon $ mkId "Q"

    (TyCon (internalName -> "Nat"), TyCon (internalName -> "Q")) ->
        Just $ TyCon $ mkId "Q"

    -- `Nat` can unify with `Ext Nat` to `Ext Nat`
    (t, TyCon (internalName -> "Nat")) | t == extendedNat ->
        Just extendedNat
    (TyCon (internalName -> "Nat"), t) | t == extendedNat ->
        Just extendedNat

    (TyApp t1 t2, TyApp t1' t2') ->
        TyApp <$> joinCoeffectTypes t1 t1' <*> joinCoeffectTypes t2 t2'

    _ -> Nothing

-- | Find out whether a coeffect if flattenable, and if so get the operation
-- | used to representing flattening on the grades
flattenable :: Type -> Type -> Maybe ((Coeffect -> Coeffect -> Coeffect), Type)
flattenable t1 t2
 | t1 == t2 = case t1 of
     t1 | t1 == extendedNat -> Just (CTimes, t1)

     TyCon (internalName -> "Nat")   -> Just (CTimes, t1)
     TyCon (internalName -> "Level") -> Just (CMeet, t1)

     -- TODO
     TyApp (TyCon (internalName -> "Interval")) t ->  flattenable t t

     _ -> Nothing
 | otherwise =
     case (t1, t2) of
        (t1, TyCon (internalName -> "Nat")) | t1 == extendedNat -> Just (CTimes, t1)
        (TyCon (internalName -> "Nat"), t2) | t2 == extendedNat -> Just (CTimes, t2)

        _ -> Just (CProduct, TyCon (mkId "×") .@ t1 .@ t2)

