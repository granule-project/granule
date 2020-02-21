{-# LANGUAGE GADTs #-}

-- Provides some helpers on kinding

module Language.Granule.Checker.KindsHelpers where

import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers

isCoeffectKind :: Kind -> Bool
isCoeffectKind (TyCon (internalName -> "Coeffect")) = True
isCoeffectKind (KUnion _ (TyCon (internalName -> "Coeffect"))) = True
isCoeffectKind (KUnion (TyCon (internalName -> "Coeffect")) _) = True
isCoeffectKind _ = False

isEffectKind :: Kind -> Bool
isEffectKind (TyCon (internalName -> "Effect")) = True
isEffectKind (KUnion _ (TyCon (internalName -> "Effect"))) = True
isEffectKind (KUnion (TyCon (internalName -> "Effect")) _) = True
isEffectKind _ = False
