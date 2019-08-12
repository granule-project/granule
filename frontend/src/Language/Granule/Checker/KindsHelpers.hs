-- Provides some helpers on kinding

module Language.Granule.Checker.KindsHelpers where

import Language.Granule.Syntax.Type

isCoeffectKind :: Kind -> Bool
isCoeffectKind KCoeffect = True
isCoeffectKind (KUnion _ KCoeffect) = True
isCoeffectKind (KUnion KCoeffect _) = True
isCoeffectKind _ = False

isEffectKind :: Kind -> Bool
isEffectKind KEffect = True
isEffectKind (KUnion _ KEffect) = True
isEffectKind (KUnion KEffect _) = True
isEffectKind _ = False
