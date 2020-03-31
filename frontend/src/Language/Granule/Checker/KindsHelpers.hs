{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

-- Provides some helpers on kinding

module Language.Granule.Checker.KindsHelpers where

import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers

isCoeffectKind :: Type (Succ (Succ Zero)) -> Bool
isCoeffectKind (TyCon (internalName -> "Coeffect")) = True
isCoeffectKind (KUnion _ (TyCon (internalName -> "Coeffect"))) = True
isCoeffectKind (KUnion (TyCon (internalName -> "Coeffect")) _) = True
isCoeffectKind _ = False

isEffectKind :: Type (Succ (Succ Zero)) -> Bool
isEffectKind (TyCon (internalName -> "Effect")) = True
isEffectKind (KUnion _ (TyCon (internalName -> "Effect"))) = True
isEffectKind (KUnion (TyCon (internalName -> "Effect")) _) = True
isEffectKind _ = False
