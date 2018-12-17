-- Provides all the type information for built-ins

module Language.Granule.Checker.Primitives where

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span

protocol = kConstr $ mkId "Protocol"

typeLevelConstructors :: [(Id, (Kind, Cardinality))] -- TODO Cardinality is not a good term
typeLevelConstructors =
    [ (mkId "()", (KType, Just 1))
    , (mkId ",", (KFun KType (KFun KType KType), Just 1))
    , (mkId "Int",  (KType, Nothing))
    , (mkId "Float", (KType, Nothing))
    , (mkId "Char", (KType, Nothing))
    , (mkId "String", (KType, Nothing))
    , (mkId "FileIO", (KFun KType KType, Nothing))
    , (mkId "Session", (KFun KType KType, Nothing))
    , (mkId "Protocol", (KType, Nothing))
    , (mkId "N", (KFun (kConstr $ mkId "Nat") KType, Just 2))
    , (mkId "Nat",  (KCoeffect, Nothing))
    , (mkId "Q",    (KCoeffect, Nothing)) -- Rationals
    , (mkId "Level", (KCoeffect, Nothing)) -- Security level
    , (mkId "Interval", (KFun KCoeffect KCoeffect, Nothing))
    , (mkId "Set", (KFun (KVar $ mkId "k") (KFun (kConstr $ mkId "k") KCoeffect), Nothing))
    , (mkId "+",   (KFun (kConstr $ mkId "Nat") (KFun (kConstr $ mkId "Nat") (kConstr $ mkId "Nat")), Nothing))
    , (mkId "*",   (KFun (kConstr $ mkId "Nat") (KFun (kConstr $ mkId "Nat") (kConstr $ mkId "Nat")), Nothing))
    , (mkId "/\\", (KFun (kConstr $ mkId "Nat") (KFun (kConstr $ mkId "Nat") (kConstr $ mkId "Nat")), Nothing))
    , (mkId "\\/", (KFun (kConstr $ mkId "Nat") (KFun (kConstr $ mkId "Nat") (kConstr $ mkId "Nat")), Nothing))
    -- File stuff
    , (mkId "Handle", (KType, Nothing))
    , (mkId "IOMode", (KType, Nothing))
    -- Channels and protocol types
    , (mkId "Send", (KFun KType (KFun protocol protocol), Nothing))
    , (mkId "Recv", (KFun KType (KFun protocol protocol), Nothing))
    , (mkId "End" , (protocol, Nothing))
    , (mkId "Chan", (KFun protocol KType, Nothing))
    , (mkId "Dual", (KFun protocol protocol, Nothing))
    , (mkId "->", (KFun KType (KFun KType KType), Nothing))
    -- Top completion on a coeffect, e.g., Ext Nat is extended naturals (with ∞)
    , (mkId "Ext", (KFun KCoeffect KCoeffect, Nothing))
    ]

dataConstructors :: [(Id, TypeScheme)]
dataConstructors =
    [ (mkId "()", Forall nullSpan [] (TyCon $ mkId "()"))
    , (mkId ",", Forall nullSpan [((mkId "a"),KType),((mkId "b"),KType)]
        (FunTy (TyVar (mkId "a"))
          (FunTy (TyVar (mkId "b"))
                 (TyApp (TyApp (TyCon (mkId ",")) (TyVar (mkId "a"))) (TyVar (mkId "b"))))))
    , (mkId "ReadMode", Forall nullSpan [] (TyCon $ mkId "IOMode"))
    , (mkId "WriteMode", Forall nullSpan [] (TyCon $ mkId "IOMode"))
    , (mkId "AppendMode", Forall nullSpan [] (TyCon $ mkId "IOMode"))
    , (mkId "ReadWriteMode", Forall nullSpan [] (TyCon $ mkId "IOMode"))
    ]

builtins :: [(Id, TypeScheme)]
builtins =
  [ (mkId "div", Forall nullSpan []
       (FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Int"))))
    -- Graded monad unit operation
  , (mkId "pure", Forall nullSpan [(mkId "a", KType)]
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
                                (TyApp (TyApp (TyCon $ mkId ",")
                                              (TyCon $ mkId "Handle"))
                                       (TyCon $ mkId "Char"))))
  , (mkId "hPutChar", Forall nullSpan [] $
                        FunTy (TyCon $ mkId "Handle")
                         (FunTy (TyCon $ mkId "Char")
                           (Diamond ["W"] (TyCon $ mkId "Handle"))))
  , (mkId "isEOF", Forall nullSpan [] $
                     FunTy (TyCon $ mkId "Handle")
                            (Diamond ["R"]
                             (TyApp (TyApp (TyCon $ mkId ",")
                                           (TyCon $ mkId "Handle"))
                                    (TyCon $ mkId "Bool"))))
  , (mkId "hClose", Forall nullSpan [] $
                        FunTy (TyCon $ mkId "Handle")
                               (Diamond ["C"] (TyCon $ mkId "()")))
    -- protocol typed primitives
  , (mkId "send", Forall nullSpan [(mkId "a", KType), (mkId "s", protocol)]
                  $ ((con "Chan") .@ (((con "Send") .@ (var "a")) .@  (var "s")))
                      .-> ((var "a")
                        .-> (Diamond ["Com"] ((con "Chan") .@ (var "s")))))

  , (mkId "recv", Forall nullSpan [(mkId "a", KType), (mkId "s", protocol)]
       $ ((con "Chan") .@ (((con "Recv") .@ (var "a")) .@  (var "s")))
         .-> (Diamond ["Com"] ((con "," .@ (var "a")) .@ ((con "Chan") .@ (var "s")))))

  , (mkId "close", Forall nullSpan [] $
                    ((con "Chan") .@ (con "End")) .-> (Diamond ["Com"] (con "()")))

  -- fork : (c -> Diamond ()) -> Diamond c'
  , (mkId "fork", Forall nullSpan [(mkId "s", protocol)] $
                    (((con "Chan") .@ (TyVar $ mkId "s")) .-> (Diamond ["Com"] (con "()")))
                    .->
                    (Diamond ["Com"] ((con "Chan") .@ ((TyCon $ mkId "Dual") .@ (TyVar $ mkId "s")))))

   -- forkRep : (c |n| -> Diamond ()) -> Diamond (c' |n|)
  , (mkId "forkRep", Forall nullSpan [(mkId "s", protocol), (mkId "n", kConstr $ mkId "Nat")] $
                    (Box (CVar $ mkId "n")
                       ((con "Chan") .@ (TyVar $ mkId "s")) .-> (Diamond ["Com"] (con "()")))
                    .->
                    (Diamond ["Com"]
                       (Box (CVar $ mkId "n")
                         ((con "Chan") .@ ((TyCon $ mkId "Dual") .@ (TyVar $ mkId "s"))))))
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
