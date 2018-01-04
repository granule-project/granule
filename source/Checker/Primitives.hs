-- Provides all the type information for built-ins

module Checker.Primitives where

import Syntax.Expr

typeLevelConstructors :: [(Id, Kind)]
typeLevelConstructors =
    map (\(name, kind) -> (mkId name, kind)) tyCs
  where
    tyCs =
        [ ("Int",  KType)
        , ("Float", KType)
        , ("List", KFun (KConstr $ mkId "Nat=") (KFun KType KType))
        , ("N", KFun (KConstr $ mkId "Nat=") KType)
        , ("One", KCoeffect)   -- Singleton coeffect
        , ("Nat",  KCoeffect)
        , ("Nat=", KCoeffect)
        , ("Nat*", KCoeffect)
        , ("Q",    KCoeffect) -- Rationals
        , ("Level", KCoeffect) -- Security level
        , ("Set", KFun (KPoly $ mkId "k") (KFun (KConstr $ mkId "k") KCoeffect))
        , ("+",   KFun (KConstr $ mkId "Nat=") (KFun (KConstr $ mkId "Nat=") (KConstr $ mkId "Nat=")))
        , ("*",   KFun (KConstr $ mkId "Nat=") (KFun (KConstr $ mkId "Nat=") (KConstr $ mkId "Nat=")))
        , ("/\\", KFun (KConstr $ mkId "Nat=") (KFun (KConstr $ mkId "Nat=") (KConstr $ mkId "Nat=")))
        , ("\\/", KFun (KConstr $ mkId "Nat=") (KFun (KConstr $ mkId "Nat=") (KConstr $ mkId "Nat=")))]

dataConstructors :: [(Id, TypeScheme)]
dataConstructors = map (\(name, kind) -> (mkId name, kind)) []

builtins :: [(Id, TypeScheme)]
builtins =
  [ -- Graded monad unit operation
    (mkId "pure", Forall nullSpan [(mkId "a", KType)]
       $ (FunTy (TyVar $ mkId "a") (Diamond [] (TyVar $ mkId "a"))))
    -- Effectful primitives
  , (mkId "toFloat", Forall nullSpan [] $ FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Float"))
  , (mkId "read", Forall nullSpan [] $ Diamond ["R"] (TyCon $ mkId "Int"))
  , (mkId "write", Forall nullSpan [] $
       FunTy (TyCon $ mkId "Int") (Diamond ["W"] (TyCon $ mkId "Int")))]

binaryOperators :: [(Operator, Type)]
binaryOperators =
  [ ("+", FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Int")))
   ,("+", FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Float")))
   ,("-", FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Int")))
   ,("-", FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Float")))
   ,("*", FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Int")))
   ,("*", FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Float")))
   ,("==", FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool")))
   ,("<=", FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool")))
   ,("<", FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool")))
   ,(">", FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool")))
   ,(">=", FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool")))
   ,("==", FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool")))
   ,("<=", FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool")))
   ,("<", FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool")))
   ,(">", FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool")))
   ,(">=", FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))) ]
