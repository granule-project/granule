-- Provides all the type information for built-ins
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}

module Language.Granule.Checker.Primitives where

import Data.List (genericLength)
import Data.List.NonEmpty (NonEmpty(..))
import Text.RawString.QQ (r)

import Language.Granule.Checker.SubstitutionContexts

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Parser (parseDefs)
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Expr (Operator(..))

nullSpanBuiltin :: Span
nullSpanBuiltin = Span (0, 0) (0, 0) "Builtin"

typeConstructors :: [(Id, (Kind, Cardinality))] -- TODO Cardinality is not a good term
typeConstructors =
    [ (mkId "ArrayStack", (KFun kNat (KFun kNat (KFun KType KType)), Nothing))
    , (mkId ",", (KFun KType (KFun KType KType), Just 1))
    , (mkId "×", (KFun KCoeffect (KFun KCoeffect KCoeffect), Just 1))
    , (mkId "Int",  (KType, Nothing))
    , (mkId "Float", (KType, Nothing))
    , (mkId "Char", (KType, Nothing))
    , (mkId "String", (KType, Nothing))
    , (mkId "IO", (KFun KType KType, Nothing))
    , (mkId "Session", (KFun KType KType, Nothing))
    , (mkId "Protocol", (KType, Nothing))
    , (mkId "Nat",  (KCoeffect, Nothing))
    , (mkId "Q",    (KCoeffect, Nothing)) -- Rationals
    , (mkId "Level", (KCoeffect, Nothing)) -- Security level
    , (mkId "Interval", (KFun KCoeffect KCoeffect, Nothing))
    , (mkId "Set", (KFun (KVar $ mkId "k") (KFun (kConstr $ mkId "k") KCoeffect), Nothing))
    -- File stuff
    -- Channels and protocol types
    , (mkId "Send", (KFun KType (KFun protocol protocol), Nothing))
    , (mkId "Recv", (KFun KType (KFun protocol protocol), Nothing))
    , (mkId "End" , (protocol, Nothing))
    , (mkId "Chan", (KFun protocol KType, Nothing))
    , (mkId "Dual", (KFun protocol protocol, Nothing))
    , (mkId "->", (KFun KType (KFun KType KType), Nothing))
    -- Top completion on a coeffect, e.g., Ext Nat is extended naturals (with ∞)
    , (mkId "Ext", (KFun KCoeffect KCoeffect, Nothing))
    ] ++ builtinTypeConstructors

tyOps :: TypeOperator -> (Kind, Kind, Kind)
tyOps = \case
    TyOpLesser -> (kNat, kNat, KPredicate)
    TyOpLesserEq -> (kNat, kNat, KPredicate)
    TyOpGreater -> (kNat, kNat, KPredicate)
    TyOpGreaterEq -> (kNat, kNat, KPredicate)
    TyOpEq -> (kNat, kNat, KPredicate)
    TyOpNotEq -> (kNat, kNat, KPredicate)
    TyOpPlus -> (kNat, kNat, kNat)
    TyOpTimes -> (kNat, kNat, kNat)
    TyOpMinus -> (kNat, kNat, kNat)
    TyOpExpon -> (kNat, kNat, kNat)
    TyOpMeet -> (kNat, kNat, kNat)
    TyOpJoin -> (kNat, kNat, kNat)

dataConstructors :: [(Id, (TypeScheme, Substitution))]
dataConstructors =
    [ ( mkId ",", (Forall nullSpanBuiltin [((mkId "a"),KType),((mkId "b"),KType)] []
        (FunTy (TyVar (mkId "a"))
          (FunTy (TyVar (mkId "b"))
                 (TyApp (TyApp (TyCon (mkId ",")) (TyVar (mkId "a"))) (TyVar (mkId "b"))))), [])
      )
    ] ++ builtinDataConstructors

builtins :: [(Id, TypeScheme)]
builtins =
  builtins' <>
  [ (mkId "div", Forall nullSpanBuiltin [] []
       (FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Int"))))
    -- Graded monad unit operation
  , (mkId "pure", Forall nullSpanBuiltin [(mkId "a", KType)] []
       $ (FunTy (TyVar $ mkId "a") (Diamond [] (TyVar $ mkId "a"))))

    -- String stuff
  , (mkId "showChar", Forall nullSpanBuiltin [] []
      $ (FunTy (TyCon $ mkId "Char") (TyCon $ mkId "String")))

    -- Effectful primitives
  , (mkId "fromStdin", Forall nullSpanBuiltin [] [] $ Diamond ["R"] (TyCon $ mkId "String"))
  , (mkId "toStdout", Forall nullSpanBuiltin [] [] $
       FunTy (TyCon $ mkId "String") (Diamond ["W"] (TyCon $ mkId "()")))
  , (mkId "toStderr", Forall nullSpanBuiltin [] [] $
       FunTy (TyCon $ mkId "String") (Diamond ["W"] (TyCon $ mkId "()")))
  , (mkId "readInt", Forall nullSpanBuiltin [] [] $ Diamond ["R"] (TyCon $ mkId "Int"))
    -- Other primitives
  , (mkId "intToFloat", Forall nullSpanBuiltin [] [] $ FunTy (TyCon $ mkId "Int")
                                                    (TyCon $ mkId "Float"))

  , (mkId "showInt", Forall nullSpanBuiltin [] [] $ FunTy (TyCon $ mkId "Int")
                                                    (TyCon $ mkId "String"))


    -- protocol typed primitives
  , (mkId "send", Forall nullSpanBuiltin [(mkId "a", KType), (mkId "s", protocol)] []
                  $ ((con "Chan") .@ (((con "Send") .@ (var "a")) .@  (var "s")))
                      .-> ((var "a")
                        .-> (Diamond ["Com"] ((con "Chan") .@ (var "s")))))

  , (mkId "recv", Forall nullSpanBuiltin [(mkId "a", KType), (mkId "s", protocol)] []
       $ ((con "Chan") .@ (((con "Recv") .@ (var "a")) .@  (var "s")))
         .-> (Diamond ["Com"] ((con "," .@ (var "a")) .@ ((con "Chan") .@ (var "s")))))

  , (mkId "close", Forall nullSpanBuiltin []  [] $
                    ((con "Chan") .@ (con "End")) .-> (Diamond ["Com"] (con "()")))

  -- fork : (c -> Diamond ()) -> Diamond c'
  , (mkId "fork", Forall nullSpanBuiltin [(mkId "s", protocol)]  [] $
                    (((con "Chan") .@ (TyVar $ mkId "s")) .-> (Diamond ["Com"] (con "()")))
                    .->
                    (Diamond ["Com"] ((con "Chan") .@ ((TyCon $ mkId "Dual") .@ (TyVar $ mkId "s")))))

   -- forkRep : (c |n| -> Diamond ()) -> Diamond (c' |n|)
  , (mkId "forkRep", Forall nullSpanBuiltin [(mkId "s", protocol), (mkId "n", kNat)] [] $
                    (Box (CVar $ mkId "n")
                       ((con "Chan") .@ (TyVar $ mkId "s")) .-> (Diamond ["Com"] (con "()")))
                    .->
                    (Diamond ["Com"]
                       (Box (CVar $ mkId "n")
                         ((con "Chan") .@ ((TyCon $ mkId "Dual") .@ (TyVar $ mkId "s"))))))
  , (mkId "unpack", Forall nullSpanBuiltin [(mkId "s", protocol)] []
                            (FunTy ((con "Chan") .@ (var "s")) (var "s")))
  ]

binaryOperators :: Operator -> NonEmpty Type
binaryOperators = \case
    OpPlus ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Int"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Float"))]
    OpMinus ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Int"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Float"))]
    OpTimes ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Int"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Float"))]
    OpEq ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))]
    OpNotEq ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))]
    OpLesserEq ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))]
    OpLesser ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))]
    OpGreater ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))]
    OpGreaterEq ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))]

-- TODO make a proper quasi quoter that parses this at compile time
builtinSrc :: String
builtinSrc = [r|

import Prelude

data () = ()



--------------------------------------------------------------------------------
-- File Handles
--------------------------------------------------------------------------------

data Handle : HandleType -> Type
  = BUILTIN

-- TODO: with type level sets we could index a handle by a set of capabilities
-- then we wouldn't need readChar and readChar' etc.
data IOMode : HandleType -> Type where
  ReadMode : IOMode R;
  WriteMode : IOMode W;
  AppendMode : IOMode A;
  ReadWriteMode : IOMode RW

data HandleType = R | W | A | RW

openHandle
  : forall {m : HandleType}
  . IOMode m
  -> String
  -> (Handle m) <Open,IOExcept>
openHandle = BUILTIN

readChar : Handle R -> (Handle R, Char) <Read,IOExcept>
readChar = BUILTIN

readChar' : Handle RW -> (Handle RW, Char) <Read,IOExcept>
readChar' = BUILTIN

appendChar : Handle A -> Char -> (Handle A) <Write,IOExcept>
appendChar = BUILTIN

writeChar : Handle W -> Char -> (Handle W) <Write,IOExcept>
writeChar = BUILTIN

writeChar' : Handle RW -> Char -> (Handle RW) <Write,IOExcept>
writeChar' = BUILTIN

closeHandle : forall {m : HandleType} . Handle m -> () <Close,IOExcept>
closeHandle = BUILTIN

isEOF : Handle R -> (Handle R, Bool) <Read,IOExcept>
isEOF = BUILTIN

isEOF' : Handle RW -> (Handle RW, Bool) <Read,IOExcept>
isEOF' = BUILTIN

-- ???
-- evalIO : forall {a : Type, e : Effect} . (a [0..1]) <IOExcept, e> -> (Maybe a) <e>
-- catch = BUILTIN
--------------------------------------------------------------------------------
-- Char
--------------------------------------------------------------------------------

-- module Char

charToInt : Char -> Int
charToInt = BUILTIN

charFromInt : Int -> Char
charFromInt = BUILTIN



--------------------------------------------------------------------------------
-- String manipulation
--------------------------------------------------------------------------------

stringAppend : String → String → String
stringAppend = BUILTIN

stringUncons : String → Maybe (Char, String)
stringUncons = BUILTIN

stringCons : Char → String → String
stringCons = BUILTIN

stringUnsnoc : String → Maybe (String, Char)
stringUnsnoc = BUILTIN

stringSnoc : String → Char → String
stringSnoc = BUILTIN

--------------------------------------------------------------------------------
-- Arrays
--------------------------------------------------------------------------------

data
  ArrayStack
    (capacity : Nat)
    (maxIndex : Nat)
    (a : Type)
  where

push
  : ∀ {a : Type, cap : Nat, maxIndex : Nat}
  . {maxIndex < cap}
  ⇒ ArrayStack cap maxIndex a
  → a
  → ArrayStack cap (maxIndex + 1) a
push = BUILTIN

pop
  : ∀ {a : Type, cap : Nat, maxIndex : Nat}
  . {maxIndex > 0}
  ⇒ ArrayStack cap maxIndex a
  → a × ArrayStack cap (maxIndex - 1) a
pop = BUILTIN

-- Boxed array, so we allocate cap words
allocate
  : ∀ {a : Type, cap : Nat}
  . N cap
  → ArrayStack cap 0 a
allocate = BUILTIN

swap
  : ∀ {a : Type, cap : Nat, maxIndex : Nat}
  . ArrayStack cap (maxIndex + 1) a
  → Fin (maxIndex + 1)
  → a
  → a × ArrayStack cap (maxIndex + 1) a
swap = BUILTIN

copy
  : ∀ {a : Type, cap : Nat, maxIndex : Nat}
  . ArrayStack cap maxIndex (a [2])
  → ArrayStack cap maxIndex a × ArrayStack cap maxIndex a
copy = BUILTIN

|]


builtinTypeConstructors :: [(Id, (Kind, Cardinality))]
builtinDataConstructors :: [(Id, (TypeScheme, Substitution))]
builtins' :: [(Id, TypeScheme)]
(builtinTypeConstructors, builtinDataConstructors, builtins') =
  (map fst datas, concatMap snd datas, map unDef defs)
    where
      AST types defs _ = case parseDefs "builtins" builtinSrc of
        Right ast -> ast
        Left err -> error err
      datas = map unData types

      unDef :: Def () () -> (Id, TypeScheme)
      unDef (Def _ name _ (Forall _ bs cs t)) = (name, Forall nullSpanBuiltin bs cs t)

      unData :: DataDecl -> ((Id, (Kind, Cardinality)), [(Id, (TypeScheme, Substitution))])
      unData (DataDecl _ tyConName tyVars kind dataConstrs)
        = (( tyConName, (maybe KType id kind, (Just $ genericLength dataConstrs)))
          , map unDataConstr dataConstrs
          )
        where
          unDataConstr :: DataConstr -> (Id, (TypeScheme, Substitution))
          unDataConstr (DataConstrIndexed _ name tysch) = (name, (tysch, []))
          unDataConstr d = unDataConstr (nonIndexedToIndexedDataConstr tyConName tyVars d)
