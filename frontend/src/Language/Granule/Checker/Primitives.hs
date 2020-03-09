-- Provides all the type information for built-ins
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}

module Language.Granule.Checker.Primitives where

import Data.List.NonEmpty (NonEmpty(..))
import Text.RawString.QQ (r)

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Parser (parseDefs)
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Expr (Operator(..))

nullSpanBuiltin :: Span
nullSpanBuiltin = Span (0, 0) (0, 0) "Builtin"

-- Given a name to the powerset of a set of particular elements,
-- where (Y, PY) in setElements means that PY is an alias for the powerset of Y.
setElements :: [(Kind, Type)]
setElements = [(KPromote $ TyCon $ mkId "IOElem", TyCon $ mkId "IO")]

-- Associates type constuctors names to their:
--    * kind
--    * cardinality (number of matchable constructors)
--    * boolean flag on whether they are indexed types or not
typeConstructors :: [(Id, (Kind, Cardinality, Bool))] -- TODO Cardinality is not a good term
typeConstructors =
    [ (mkId "×", (KFun KCoeffect (KFun KCoeffect KCoeffect), Just 1, False))
    , (mkId "Int",  (KType, Nothing, False))
    , (mkId "Float", (KType, Nothing, False))
    , (mkId "DFloat", (KType, Nothing, False))
    , (mkId "Char", (KType, Nothing, False))
    , (mkId "String", (KType, Nothing, False))
    , (mkId "Protocol", (KType, Nothing, False))
    , (mkId "Nat",  (KUnion KCoeffect KEffect, Nothing, False))
    , (mkId "Q",    (KCoeffect, Nothing, False)) -- Rationals
    , (mkId "Level", (KCoeffect, Nothing, False)) -- Security level
    , (mkId "Private", (KPromote (TyCon $ mkId "Level"), Nothing, False))
    , (mkId "Public", (KPromote (TyCon $ mkId "Level"), Nothing, False))
    , (mkId "Unused", (KPromote (TyCon $ mkId "Level"), Nothing, False))
    , (mkId "Interval", (KFun KCoeffect KCoeffect, Nothing, False))
    , (mkId "Set", (KFun (KVar $ mkId "k") (KFun (kConstr $ mkId "k") KCoeffect), Nothing, False))
    -- Channels and protocol types
    , (mkId "Send", (KFun KType (KFun protocol protocol), Nothing, False))
    , (mkId "Recv", (KFun KType (KFun protocol protocol), Nothing, False))
    , (mkId "End" , (protocol, Nothing, False))
    , (mkId "Chan", (KFun protocol KType, Nothing, True))
    , (mkId "Dual", (KFun protocol protocol, Nothing, True))
    , (mkId "->", (KFun KType (KFun KType KType), Nothing, False))
    -- Top completion on a coeffect, e.g., Ext Nat is extended naturals (with ∞)
    , (mkId "Ext", (KFun KCoeffect KCoeffect, Nothing, True))
    -- Effect grade types - Sessions
    , (mkId "Session", (KPromote (TyCon $ mkId "Com"), Nothing, True))
    , (mkId "Com", (KEffect, Nothing, False))
    -- Effect grade types - IO
    , (mkId "IO", (KEffect, Nothing, False))
    , (mkId "Stdout", (KPromote (TyCon $ mkId "IOElem"), Nothing, False))
    , (mkId "Stdin", (KPromote (TyCon $ mkId "IOElem"), Nothing, False))
    , (mkId "Stderr", (KPromote (TyCon $ mkId "IOElem"), Nothing, False))
    , (mkId "Open", (KPromote (TyCon $ mkId "IOElem"), Nothing, False))
    , (mkId "Read", (KPromote (TyCon $ mkId "IOElem"), Nothing, False))
    , (mkId "Write", (KPromote (TyCon $ mkId "IOElem"), Nothing, False))
    , (mkId "IOExcept", (KPromote (TyCon $ mkId "IOElem"), Nothing, False))
    , (mkId "Close", (KPromote (TyCon $ mkId "IOElem"), Nothing, False))
    ]

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

dataTypes :: [DataDecl]
dataTypes =
    -- Special built-in for products (which cannot be parsed)
    [ DataDecl
      { dataDeclSpan = nullSpanBuiltin
      , dataDeclId   = mkId ","
      , dataDeclTyVarCtxt = [((mkId "a"),KType),((mkId "b"),KType)]
      , dataDeclKindAnn = Just KType
      , dataDeclDataConstrs = [
        DataConstrNonIndexed
          { dataConstrSpan = nullSpanBuiltin
          , dataConstrId = mkId ","
          , dataConstrParams = [TyVar (mkId "a"), TyVar (mkId "b")]
         }]}
    ] ++ builtinDataTypesParsed

binaryOperators :: Operator -> NonEmpty Type
binaryOperators = \case
    OpPlus ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Int"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Float")),
          FunTy (TyCon $ mkId "DFloat") (FunTy (TyCon $ mkId "DFloat") (TyCon $ mkId "DFloat"))]
    OpMinus ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Int"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Float")),
          FunTy (TyCon $ mkId "DFloat") (FunTy (TyCon $ mkId "DFloat") (TyCon $ mkId "DFloat"))]
    OpTimes ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Int"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Float"))]
    OpDiv ->
      FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Float"))
      :| [FunTy (TyCon $ mkId "DFloat") (FunTy (TyCon $ mkId "DFloat") (TyCon $ mkId "DFloat"))]
    OpEq ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool")),
          FunTy (TyCon $ mkId "DFloat") (FunTy (TyCon $ mkId "DFloat") (TyCon $ mkId "Bool"))]
    OpNotEq ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool")),
          FunTy (TyCon $ mkId "DFloat") (FunTy (TyCon $ mkId "DFloat") (TyCon $ mkId "Bool"))]
    OpLesserEq ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool")),
          FunTy (TyCon $ mkId "DFloat") (FunTy (TyCon $ mkId "DFloat") (TyCon $ mkId "Bool"))]
    OpLesser ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool")),
          FunTy (TyCon $ mkId "DFloat") (FunTy (TyCon $ mkId "DFloat") (TyCon $ mkId "Bool"))]
    OpGreater ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool")),
          FunTy (TyCon $ mkId "DFloat") (FunTy (TyCon $ mkId "DFloat") (TyCon $ mkId "Bool"))]
    OpGreaterEq ->
      FunTy (TyCon $ mkId "Int") (FunTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [FunTy (TyCon $ mkId "Float") (FunTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool")),
          FunTy (TyCon $ mkId "DFloat") (FunTy (TyCon $ mkId "DFloat") (TyCon $ mkId "Bool"))]

-- TODO make a proper quasi quoter that parses this at compile time
builtinSrc :: String
builtinSrc = [r|

import Prelude

data () = ()

--------------------------------------------------------------------------------
-- Arithmetic
--------------------------------------------------------------------------------

div : Int -> Int -> Int
div = BUILTIN

--------------------------------------------------------------------------------
-- Graded Possiblity
--------------------------------------------------------------------------------

pure
  : forall {a : Type}
  . a -> a <>
pure = BUILTIN

--------------------------------------------------------------------------------
-- I/O
--------------------------------------------------------------------------------

fromStdin : String <{Stdin}>
fromStdin = BUILTIN

toStdout : String -> () <{Stdout}>
toStdout = BUILTIN

toStderr : String -> () <{Stderr}>
toStderr = BUILTIN

readInt : Int <{Stdin}>
readInt = BUILTIN

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

showChar : Char -> String
showChar = BUILTIN

intToFloat : Int -> Float
intToFloat = BUILTIN

showInt : Int -> String
showInt = BUILTIN

--------------------------------------------------------------------------------
-- Thread / Sessions
--------------------------------------------------------------------------------

fork
  : forall {s : Protocol, k : Coeffect, c : k}
  . ((Chan s) [c] -> () <Session>) -> ((Chan (Dual s)) [c]) <Session>
fork = BUILTIN

forkLinear
  : forall {s : Protocol}
  . (Chan s -> () <Session>) -> (Chan (Dual s)) <Session>
forkLinear = BUILTIN

send
  : forall {a : Type, s : Protocol}
  . Chan (Send a s) -> a -> (Chan s) <Session>
send = BUILTIN

recv
  : forall {a : Type, s : Protocol}
  . Chan (Recv a s) -> (a, Chan s) <Session>
recv = BUILTIN

close : Chan End -> () <Session>
close = BUILTIN

unpackChan
  : forall {s : Protocol}
  . Chan s -> s
unpackChan = BUILTIN

--------------------------------------------------------------------------------
-- File Handles
--------------------------------------------------------------------------------

data Handle : HandleType -> Type where

data HandleType = R | W | A | RW

-- TODO: with type level sets we could index a handle by a set of capabilities
-- then we wouldn't need readChar and readChar' etc.
data IOMode : HandleType -> Type where
  ReadMode : IOMode R;
  WriteMode : IOMode W;
  AppendMode : IOMode A;
  ReadWriteMode : IOMode RW

openHandle
  : forall {m : HandleType}
  . IOMode m
  -> String
  -> (Handle m) <{Open,IOExcept}>
openHandle = BUILTIN

readChar : Handle R -> (Handle R, Char) <{Read,IOExcept}>
readChar = BUILTIN

readChar' : Handle RW -> (Handle RW, Char) <{Read,IOExcept}>
readChar' = BUILTIN

appendChar : Handle A -> Char -> (Handle A) <{Write,IOExcept}>
appendChar = BUILTIN

writeChar : Handle W -> Char -> (Handle W) <{Write,IOExcept}>
writeChar = BUILTIN

writeChar' : Handle RW -> Char -> (Handle RW) <{Write,IOExcept}>
writeChar' = BUILTIN

closeHandle : forall {m : HandleType} . Handle m -> () <{Close,IOExcept}>
closeHandle = BUILTIN

isEOF : Handle R -> (Handle R, Bool) <{Read,IOExcept}>
isEOF = BUILTIN

isEOF' : Handle RW -> (Handle RW, Bool) <{Read,IOExcept}>
isEOF' = BUILTIN


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

--------------------------------------------------------------------------------
-- Cost
--------------------------------------------------------------------------------

tick : () <1>
tick = BUILTIN

--------------------------------------------------------------------------------
-- L3-style pointers (work in progress)
--------------------------------------------------------------------------------

-- data Ptr : Type -> Type where

-- data Cap : Type -> Type -> Type where

-- data PtrCap a where
--   MkPtrCap : forall { id : Type } . (Ptr id) [] -> Cap a id -> PtrCap a

-- newPtr
--   : forall { a : Type }
--   . a -> PtrCap a
-- newPtr = BUILTIN

-- swapPtr
--   : forall { a b : Type, id : Type }
--   . b -> Ptr id -> Cap a id -> (a × Cap b id)
-- swapPtr = BUILTIN

-- freePtr
--   : forall { a b : Type, id : Type }
--   . Ptr id -> Cap a id -> a
-- freePtr = BUILTIN


|]


builtinDataTypesParsed :: [DataDecl]
builtins :: [(Id, TypeScheme)]
(builtinDataTypesParsed, builtins) =
  (types, map unDef defs)
    where
      AST types defs _ _ _ = case parseDefs "builtins" builtinSrc of
        Right ast -> ast
        Left err -> error err

      unDef :: Def () () -> (Id, TypeScheme)
      unDef (Def _ name _ (Forall _ bs cs t)) = (name, Forall nullSpanBuiltin bs cs t)
