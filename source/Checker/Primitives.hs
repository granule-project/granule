-- Provides all the type information for built-ins

module Checker.Primitives where

import Syntax.Expr

typeLevelConstructors :: [(ConstructorId, Kind)]
typeLevelConstructors =
  [ ("Int",  KType)
  , ("Float", KType)
  , ("Bool", KType)
  , ("List", KFun (KConstr "Nat=") (KFun KType KType))
  , ("N", KFun (KConstr "Nat=") KType)
  , ("One", KCoeffect)   -- Singleton coeffect
  , ("Nat",  KCoeffect)
  , ("Nat=", KCoeffect)
  , ("Nat*", KCoeffect)
  , ("Q",    KCoeffect) -- Rationals
  , ("Level", KCoeffect) -- Security level
  , ("Set", KFun (KPoly $ mkId "k") (KFun (KConstr "k") KCoeffect))
  , ("+",   KFun (KConstr "Nat=") (KFun (KConstr "Nat=") (KConstr "Nat=")))
  , ("*",   KFun (KConstr "Nat=") (KFun (KConstr "Nat=") (KConstr "Nat=")))
  , ("/\\", KFun (KConstr "Nat=") (KFun (KConstr "Nat=") (KConstr "Nat=")))
  , ("\\/", KFun (KConstr "Nat=") (KFun (KConstr "Nat=") (KConstr "Nat=")))]

dataConstructors :: [(ConstructorId, TypeScheme)]
dataConstructors =
  [ ("True", Forall nullSpan [] (TyCon "Bool"))
  , ("False", Forall nullSpan [] (TyCon "Bool")) ]

builtins :: [(Id, TypeScheme)]
builtins =
  [ -- Graded monad unit operation
    (mkId "pure", Forall nullSpan [(mkId "a", KType)]
       $ (FunTy (TyVar $ mkId "a") (Diamond [] (TyVar $ mkId "a"))))
    -- Effectful primitives
  , (mkId "toFloat", Forall nullSpan [] $ FunTy (TyCon "Int") (TyCon "Float"))
  , (mkId "read", Forall nullSpan [] $ Diamond ["R"] (TyCon "Int"))
  , (mkId "write", Forall nullSpan [] $
       FunTy (TyCon "Int") (Diamond ["W"] (TyCon "Int")))]

binaryOperators :: [(Operator, Type)]
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
