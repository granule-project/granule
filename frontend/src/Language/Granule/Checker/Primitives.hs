-- Provides all the type information for built-ins
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}

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
setElements :: [(Kind, Type Zero)]
setElements = [(TyCon $ mkId "IOElem", TyCon $ mkId "IO")]

kindConstructor :: [(Id, (Type (Succ One), Cardinality, Bool))]
kindConstructor =
  [ (mkId "Coeffect", (Type (LSucc LZero), Nothing, False))
  , (mkId "Effect", (Type (LSucc LZero), Nothing, False))
  , (mkId "Predicate", (Type (LSucc LZero), Nothing, False)) ]

-- Associates type constuctors names to their:
--    * kind
--    * cardinality (number of matchable constructors)
--    * boolean flag on whether they are indexed types or not
typeConstructors :: [(Id, (Type One, Cardinality, Bool))] -- TODO Cardinality is not a good term
typeConstructors =
    [ (mkId "->", (FunTy (Type LZero) (FunTy (Type LZero) (Type LZero)), Nothing, False))
    , (mkId "×", (FunTy (tyCon $ "Coeffect") (FunTy (tyCon $ "Coeffect") (tyCon $ "Coeffect")), Just 1, False))
    , (mkId "Int",  (Type LZero, Nothing, False))
    , (mkId "Float", (Type LZero, Nothing, False))
    , (mkId "Char", (Type LZero, Nothing, False))
    , (mkId "String", (Type LZero, Nothing, False))
    , (mkId "Protocol", (Type LZero, Nothing, False))
    , (mkId "Nat",  (KUnion (tyCon "Coeffect") (tyCon "Effect"), Nothing, False))
    , (mkId "Q",    (tyCon "Coeffect", Nothing, False)) -- Rationals
    , (mkId "Level", (tyCon "Coeffect", Nothing, False)) -- Security level
    , (mkId "Interval", (FunTy (tyCon "Coeffect") (tyCon "Coeffect"), Nothing, False))
    , (mkId "Set", (FunTy (TyVar $ mkId "k") (FunTy (tyCon "k") (tyCon "Coeffect")), Nothing, False))
    -- Channels and protocol types
    , (mkId "Send", (FunTy (Type LZero) (FunTy protocol protocol), Nothing, False))
    , (mkId "Recv", (FunTy (Type LZero) (FunTy protocol protocol), Nothing, False))
    , (mkId "End" , (protocol, Nothing, False))
    , (mkId "Chan", (FunTy protocol (Type LZero), Nothing, True))
    , (mkId "Dual", (FunTy protocol protocol, Nothing, True))
    , (mkId "->", (FunTy (Type LZero) (FunTy (Type LZero) (Type LZero)), Nothing, False))
    -- Top completion on a coeffect, e.g., Ext Nat is extended naturals (with ∞)
    , (mkId "Ext", (FunTy (tyCon "Coeffect") (tyCon "Coeffect"), Nothing, True))
    -- Effect grade types - Sessions
    , (mkId "Session", (TyCon $ mkId "Com", Nothing, True))
    , (mkId "Com", ((tyCon "Effect"), Nothing, False))
    -- Effect grade types - IO
    , (mkId "IO", ((tyCon "Effect"), Nothing, False))
    , (mkId "Stdout", (TyCon $ mkId "IOElem", Nothing, False))
    , (mkId "Stdin", (TyCon $ mkId "IOElem", Nothing, False))
    , (mkId "Stderr", (TyCon $ mkId "IOElem", Nothing, False))
    , (mkId "Open", (TyCon $ mkId "IOElem", Nothing, False))
    , (mkId "Read", (TyCon $ mkId "IOElem", Nothing, False))
    , (mkId "Write", (TyCon $ mkId "IOElem", Nothing, False))
    , (mkId "IOExcept", (TyCon $ mkId "IOElem", Nothing, False))
    , (mkId "Close", (TyCon $ mkId "IOElem", Nothing, False))
    ]

tyOps :: TypeOperator -> (Kind, Kind, Kind)
tyOps = \case
    TyOpLesser -> (kNat, kNat, (TyCon (mkId "Predicate")))
    TyOpLesserEq -> (kNat, kNat, (TyCon (mkId "Predicate")))
    TyOpGreater -> (kNat, kNat, (TyCon (mkId "Predicate")))
    TyOpGreaterEq -> (kNat, kNat, (TyCon (mkId "Predicate")))
    TyOpEq -> (kNat, kNat, (TyCon (mkId "Predicate")))
    TyOpNotEq -> (kNat, kNat, (TyCon (mkId "Predicate")))
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
      , dataDeclTyVarCtxt = [((mkId "a"), Type LZero),((mkId "b"), Type LZero)]
      , dataDeclKindAnn = Just (Type LZero)
      , dataDeclDataConstrs = [
        DataConstrNonIndexed
          { dataConstrSpan = nullSpanBuiltin
          , dataConstrId = mkId ","
          , dataConstrParams = [TyVar (mkId "a"), TyVar (mkId "b")]
         }]}
    ] ++ builtinDataTypesParsed

binaryOperators :: Operator -> NonEmpty (Type Zero)
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