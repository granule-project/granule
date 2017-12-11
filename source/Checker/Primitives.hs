-- Provides all the type information for built-ins

module Checker.Primitives where

import Syntax.Expr

typeLevelConstructors :: [(Id, Kind)]
typeLevelConstructors =
  [ ("Int",  KType)
  , ("Float", KType)
  , ("Bool", KType)
  , ("List", KFun (KConstr "Nat") (KFun KType KType))
  , ("N", KFun (KConstr "Nat") KType)
  , ("One", KCoeffect)   -- Singleton coeffect
  , ("Nat",  KCoeffect)
  , ("Nat=", KCoeffect)
  , ("Nat*", KCoeffect)
  , ("Q",    KCoeffect) -- Rationals
  , ("Level", KCoeffect) -- Security level
  , ("Set", KFun (KPoly "k") (KFun (KConstr "k") KCoeffect))
  , ("+",   KFun (KConstr "Nat=") (KFun (KConstr "Nat=") (KConstr "Nat=")))
  , ("*",   KFun (KConstr "Nat=") (KFun (KConstr "Nat=") (KConstr "Nat=")))
  , ("/\\", KFun (KConstr "Nat=") (KFun (KConstr "Nat=") (KConstr "Nat=")))
  , ("\\/", KFun (KConstr "Nat=") (KFun (KConstr "Nat=") (KConstr "Nat=")))]

dataConstructors :: [(Id, TypeScheme)]
dataConstructors =
  [ ("True", Forall nullSpan [] (TyCon "Bool"))
  , ("False", Forall nullSpan [] (TyCon "Bool")) ]

builtins :: [(Id, TypeScheme)]
builtins =
  [ -- Graded monad unit operation
    ("pure", Forall nullSpan [("a", KType)]
       $ (FunTy (TyVar "a") (Diamond [] (TyVar "a"))))
    -- Effectful primitives
  , ("toFloat", Forall nullSpan [] $ FunTy (TyCon "Int") (TyCon "Float"))
  , ("read", Forall nullSpan [] $ Diamond ["R"] (TyCon "Int"))
  , ("write", Forall nullSpan [] $
       FunTy (TyCon "Int") (Diamond ["W"] (TyCon "Int")))]

binaryOperators :: [(Id, Type)]
binaryOperators =
  [ ("+", FunTy (TyCon "Int") (FunTy (TyCon "Int") (TyCon "Int")))
   ,("+", FunTy (TyCon "Float") (FunTy (TyCon "Float") (TyCon "Float")))
   ,("-", FunTy (TyCon "Int") (FunTy (TyCon "Int") (TyCon "Int")))
   ,("-", FunTy (TyCon "Float") (FunTy (TyCon "Float") (TyCon "Float")))
   ,("*", FunTy (TyCon "Int") (FunTy (TyCon "Int") (TyCon "Int")))
   ,("*", FunTy (TyCon "Float") (FunTy (TyCon "Float") (TyCon "Float")))
   ,("==", FunTy (TyCon "Int") (FunTy (TyCon "Int") (TyCon "Bool")))
   ,("<=", FunTy (TyCon "Int") (FunTy (TyCon "Int") (TyCon "Bool")))
   ,("<", FunTy (TyCon "Int") (FunTy (TyCon "Int") (TyCon "Bool")))
   ,(">", FunTy (TyCon "Int") (FunTy (TyCon "Int") (TyCon "Bool")))
   ,(">=", FunTy (TyCon "Int") (FunTy (TyCon "Int") (TyCon "Bool")))
   ,("==", FunTy (TyCon "Float") (FunTy (TyCon "Float") (TyCon "Bool")))
   ,("<=", FunTy (TyCon "Float") (FunTy (TyCon "Float") (TyCon "Bool")))
   ,("<", FunTy (TyCon "Float") (FunTy (TyCon "Float") (TyCon "Bool")))
   ,(">", FunTy (TyCon "Float") (FunTy (TyCon "Float") (TyCon "Bool")))
   ,(">=", FunTy (TyCon "Float") (FunTy (TyCon "Float") (TyCon "Bool"))) ]