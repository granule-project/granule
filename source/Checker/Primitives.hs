-- Provides all the type information for built-ins

module Checker.Primitives where

import Syntax.Expr

typeLevelConstructors :: [(Id, Kind)]
typeLevelConstructors =
  [ ("Int",  KType)
  , ("Bool", KType)
  , ("List", KFun (KConstr "Nat") (KFun KType KType))
  , ("One", KCoeffect)   -- Singleton coeffect
  , ("Nat",  KCoeffect)
  , ("Nat=", KCoeffect)
  , ("Nat*", KCoeffect)
  , ("Q",    KCoeffect) -- Rationals
  , ("Level", KCoeffect) -- Security level
  , ("Set", KFun (KPoly "k") (KFun (KConstr "k") KCoeffect)) ]
