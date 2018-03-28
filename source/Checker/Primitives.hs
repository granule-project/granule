-- Provides all the type information for built-ins

module Checker.Primitives where

import Syntax.Expr

session = KConstr $ mkId "Session"

typeLevelConstructors :: [(Id, (Kind, Cardinality))]
typeLevelConstructors =
    [ (mkId $ "()", (KType, Just 1))
    , (mkId $ "Int",  (KType, Nothing))
    , (mkId $ "Float", (KType, Nothing))
    , (mkId $ "Char", (KType, Nothing))
    , (mkId $ "String", (KType, Nothing))
    , (mkId $ "FileIO", (KFun KType KType, Nothing))
    , (mkId $ "Session", (KFun KType KType, Nothing))
    , (mkId $ "List", (KFun (KConstr $ mkId "Nat=") (KFun KType KType), Just 2))
    , (mkId $ "N", (KFun (KConstr $ mkId "Nat=") KType, Just 2))
    , (mkId $ "Cartesian", (KCoeffect, Nothing))   -- Singleton coeffect
    , (mkId $ "Nat",  (KCoeffect, Nothing))
    , (mkId $ "Nat=", (KCoeffect, Nothing))
    , (mkId $ "Nat*", (KCoeffect, Nothing))
    , (mkId $ "Q",    (KCoeffect, Nothing)) -- Rationals
    , (mkId $ "Level", (KCoeffect, Nothing)) -- Security level
    , (mkId $ "Set", (KFun (KPoly $ mkId "k") (KFun (KConstr $ mkId "k") KCoeffect), Nothing))
    , (mkId $ "+",   (KFun (KConstr $ mkId "Nat=") (KFun (KConstr $ mkId "Nat=") (KConstr $ mkId "Nat=")), Nothing))
    , (mkId $ "*",   (KFun (KConstr $ mkId "Nat=") (KFun (KConstr $ mkId "Nat=") (KConstr $ mkId "Nat=")), Nothing))
    , (mkId $ "/\\", (KFun (KConstr $ mkId "Nat=") (KFun (KConstr $ mkId "Nat=") (KConstr $ mkId "Nat=")), Nothing))
    , (mkId $ "\\/", (KFun (KConstr $ mkId "Nat=") (KFun (KConstr $ mkId "Nat=") (KConstr $ mkId "Nat=")), Nothing))
    -- File stuff
    , (mkId $ "Handle", (KType, Nothing))
    -- Channels and session types
    , (mkId $ "Send", (KFun KType (KFun session session), Nothing))
    , (mkId $ "Recv", (KFun KType (KFun session session), Nothing))
    , (mkId $ "End" , (session, Nothing))
    , (mkId $ "Chan", (KFun session KType, Nothing))
    ]

dataConstructors :: [(Id, TypeScheme)]
dataConstructors =
    [(mkId $ "()", Forall nullSpan [] (TyCon $ mkId "()"))]

builtins :: [(Id, TypeScheme)]
builtins =
  [ -- Graded monad unit operation
    (mkId "pure", Forall nullSpan [(mkId "a", KType)]
       $ (FunTy (TyVar $ mkId "a") (Diamond [] (TyVar $ mkId "a"))))

    -- String stuff
  , (mkId "stringAppend", Forall nullSpan []
      $ (FunTy (TyCon $ mkId "String") (FunTy (TyCon $ mkId "String") (TyCon $ mkId "String"))))
  , (mkId "showChar", Forall nullSpan []
      $ (FunTy (TyCon $ mkId "Char") (TyCon $ mkId "String")))

    -- Effectful primitives
  , (mkId "read", Forall nullSpan [] $ Diamond ["R"] (TyCon $ mkId "String"))
  , (mkId "write", Forall nullSpan [] $
       FunTy (TyCon $ mkId "String") (Diamond ["W"] (TyCon $ mkId "()")))
  , (mkId "readInt", Forall nullSpan [] $ Diamond ["R"] (TyCon $ mkId "Int"))
    -- Other primitives
  , (mkId "intToFloat", Forall nullSpan [] $ FunTy (TyCon $ mkId "Int")
                                                    (TyCon $ mkId "Float"))

  , (mkId "showInt", Forall nullSpan [] $ FunTy (TyCon $ mkId "Int")
                                                    (TyCon $ mkId "String"))

    -- File stuff
  , (mkId "openFile", Forall nullSpan [] $
                        FunTy (TyCon $ mkId "String")
                          (FunTy (TyCon $ mkId "IOMode")
                                (Diamond ["O"] (TyCon $ mkId "Handle"))))
  , (mkId "hGetChar", Forall nullSpan [] $
                        FunTy (TyCon $ mkId "Handle")
                               (Diamond ["RW"]
                                (PairTy (TyCon $ mkId "Handle") (TyCon $ mkId "Char"))))
  , (mkId "hPutChar", Forall nullSpan [] $
                        FunTy (TyCon $ mkId "Handle")
                         (FunTy (TyCon $ mkId "Char")
                           (Diamond ["W"] (TyCon $ mkId "Handle"))))
  , (mkId "isEOF", Forall nullSpan [] $
                     FunTy (TyCon $ mkId "Handle")
                            (Diamond ["R"] (PairTy (TyCon $ mkId "Handle")
                                                    (TyCon $ mkId "Bool"))))
  , (mkId "hClose", Forall nullSpan [] $
                        FunTy (TyCon $ mkId "Handle")
                               (Diamond ["C"] (TyCon $ mkId "()")))
    -- Session typed primitives
  , (mkId "send", Forall nullSpan [(mkId "a", KType), (mkId "s", session)]
                  $ ((con "Chan") .@ (((con "Send") .@ (var "a")) .@  (var "s")))
                      .-> ((var "a")
                        .-> (Diamond ["Com"] ((con "Chan") .@ (var "s")))))

  , (mkId "recv", Forall nullSpan [(mkId "a", KType), (mkId "s", session)]
       $ ((con "Chan") .@ (((con "Recv") .@ (var "a")) .@  (var "s")))
         .-> (Diamond ["Com"] (PairTy (var "a") ((con "Chan") .@ (var "s")))))

  , (mkId "close", Forall nullSpan [] $
                    ((con "Chan") .@ (con "End")) .-> (Diamond ["Com"] (con "()")))
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
