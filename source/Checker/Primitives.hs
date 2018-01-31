-- Provides all the type information for built-ins

module Checker.Primitives where

import Syntax.Expr

session = KConstr $ mkId "Session"

typeLevelConstructors :: [(Id, Kind)]
typeLevelConstructors =
    [ (mkId $ "Unit", KType)
    , (mkId $ "Int",  KType)
    , (mkId $ "Float", KType)
    , (mkId $ "List", KFun (KConstr $ mkId "Nat=") (KFun KType KType))
    , (mkId $ "N", KFun (KConstr $ mkId "Nat=") KType)
    , (mkId $ "One", KCoeffect)   -- Singleton coeffect
    , (mkId $ "Nat",  KCoeffect)
    , (mkId $ "Nat=", KCoeffect)
    , (mkId $ "Nat*", KCoeffect)
    , (mkId $ "Q",    KCoeffect) -- Rationals
    , (mkId $ "Level", KCoeffect) -- Security level
    , (mkId $ "Set", KFun (KPoly $ mkId "k") (KFun (KConstr $ mkId "k") KCoeffect))
    , (mkId $ "+",   KFun (KConstr $ mkId "Nat=") (KFun (KConstr $ mkId "Nat=") (KConstr $ mkId "Nat=")))
    , (mkId $ "*",   KFun (KConstr $ mkId "Nat=") (KFun (KConstr $ mkId "Nat=") (KConstr $ mkId "Nat=")))
    , (mkId $ "/\\", KFun (KConstr $ mkId "Nat=") (KFun (KConstr $ mkId "Nat=") (KConstr $ mkId "Nat=")))
    , (mkId $ "\\/", KFun (KConstr $ mkId "Nat=") (KFun (KConstr $ mkId "Nat=") (KConstr $ mkId "Nat=")))
    -- Channels and session types
    , (mkId $ "Send", KFun KType (KFun session session))
    , (mkId $ "Recv", KFun KType (KFun session session))
    , (mkId $ "End" , session)
    , (mkId $ "Chan", KFun session KType)
    ]

dataConstructors :: [(Id, TypeScheme)]
dataConstructors =
    [(mkId $ "Unit", Forall nullSpan [] (TyCon $ mkId "Unit"))]

builtins :: [(Id, TypeScheme)]
builtins =
  [ -- Graded monad unit operation
    (mkId "pure", Forall nullSpan [(mkId "a", KType)]
       $ (FunTy (TyVar $ mkId "a") (Diamond [] (TyVar $ mkId "a"))))

    -- Effectful primitives
  , (mkId "read", Forall nullSpan [] $ Diamond ["R"] (TyCon $ mkId "Int"))
  , (mkId "write", Forall nullSpan [] $
       FunTy (TyCon $ mkId "Int") (Diamond ["W"] (TyCon $ mkId "Unit")))

    -- Other primitives
  , (mkId "intToFloat", Forall nullSpan [] $ FunTy (TyCon $ mkId "Int")
                                                    (TyCon $ mkId "Float"))

    -- Session typed primitives
  , (mkId "send", Forall nullSpan [(mkId "a", KType), (mkId "s", session)]
                  $ ((con "Chan") .@ (((con "Send") .@ (var "a")) .@  (var "s")))
                      .-> ((var "a")
                        .-> ((con "Chan") .@ (var "s"))))

  , (mkId "recv", Forall nullSpan [(mkId "a", KType), (mkId "s", session)]
       $ ((con "Chan") .@ (((con "Recv") .@ (var "a")) .@  (var "s")))
         .-> (PairTy (var "a") ((con "Chan") .@ (var "s"))))

  , (mkId "close", Forall nullSpan [] $ ((con "Chan") .@ (con "End")) .-> (con "Unit"))
  ]

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
