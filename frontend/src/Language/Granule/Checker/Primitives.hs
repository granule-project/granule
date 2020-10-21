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
-- where (Y, PY) in setElements means that PY is an alias for the powerset of Y

-- e.g. {Stdin} in Set IOElem in Effect
-- and  {Stdin} in IO         in Effect

setElements :: [(Type, Type)]
setElements = [(TyCon $ mkId "IOElem", TyCon $ mkId "IO")]

kindConstructor :: [(Id, (Type, [Id], Bool))]
kindConstructor =
  [ (mkId "Coeffect",  (Type 0, [], False))
  , (mkId "Effect",    (Type 0, [], False))
  , (mkId "Predicate", (Type 0, [], False)) ]

-- Associates type constuctors names to their:
--    * kind
--    * list of (finite) matchable constructor names (but not the actual set of constructor names which could be infinite)
--    * boolean flag on whether they are indexed types or not
typeConstructors :: [(Id, (Type, [Id], Bool))] -- TODO Cardinality is not a good term
typeConstructors =
    [ (mkId "->",     (funTy (Type 0) (funTy (Type 0) (Type 0)), [], False))
    , (mkId "×",      (funTy kcoeffect (funTy kcoeffect kcoeffect), [mkId ", "], False))
    , (mkId "Int",    (Type 0, [], False))
    , (mkId "Float",  (Type 0, [], False))
    , (mkId "Char",   (Type 0, [], False))
    , (mkId "String", (Type 0, [], False))
    , (mkId "Protocol", (Type 0, [], False))
    -- Coeffect types
    , (mkId "Nat",      (kcoeffect, [], False))
    , (mkId "Q",        (kcoeffect, [], False)) -- Rationals
    , (mkId "OOZ",      (kcoeffect, [], False)) -- 1 + 1 = 0
    -- Security levels
    , (mkId "Level",    (kcoeffect, [], False)) -- Security level
    , (mkId "Private",  (tyCon "Level", [], False))
    , (mkId "Public",   (tyCon "Level", [], False))
    , (mkId "Unused",   (tyCon "Level", [], False))
    -- Other coeffect constructors
    , (mkId "Infinity", ((tyCon "Ext") .@ (tyCon "Nat"), [], False))
    , (mkId "Interval", (kcoeffect .-> kcoeffect, [], False))
    , (mkId "Set", ((TyVar $ mkId "k") .-> ((tyCon "k") .-> kcoeffect), [], False))
    -- Channels and protocol types
    , (mkId "Send", (funTy (Type 0) (funTy protocol protocol), [], False))
    , (mkId "Recv", (funTy (Type 0) (funTy protocol protocol), [], False))
    , (mkId "End" , (protocol, [], False))
    , (mkId "Chan", (funTy protocol (Type 0), [], True))
    , (mkId "LChan", (funTy protocol (Type 0), [], True))
    , (mkId "Dual", (funTy protocol protocol, [], True))
    , (mkId "->", (funTy (Type 0) (funTy (Type 0) (Type 0)), [], False))
    -- Top completion on a coeffect, e.g., Ext Nat is extended naturals (with ∞)
    , (mkId "Ext", (funTy kcoeffect kcoeffect, [], True))
    -- Effect grade types - Sessions
    , (mkId "Session",  (tyCon "Com", [], True))
    , (mkId "Com",      (keffect, [], False))
    -- Effect grade types - IO
    , (mkId "IOElem",   (ktype, [], False))
    , (mkId "IO",       (keffect, [], False))
    , (mkId "Stdout",   (tyCon "IOElem", [], False))
    , (mkId "Stdin",    (tyCon "IOElem", [], False))
    , (mkId "Stderr",   (tyCon "IOElem", [], False))
    , (mkId "Open",     (tyCon "IOElem", [], False))
    , (mkId "Read",     (tyCon "IOElem", [], False))
    , (mkId "Write",    (tyCon "IOElem", [], False))
    , (mkId "IOExcept", (tyCon "IOElem", [], False))
    , (mkId "Close",    (tyCon "IOElem", [], False))

    --Effect grade types - Exceptions
    , (mkId "Exception", (keffect, [], False))
    , (mkId "Success", (tyCon "Exception", [], False))
    , (mkId "MayFail", (tyCon "Exception", [], False))
    ]

-- Various predicates and functions on type operators
closedOperation :: TypeOperator -> Bool
closedOperation =
  \case
    TyOpPlus -> True
    TyOpTimes -> True
    TyOpMinus -> True
    TyOpExpon -> True
    TyOpMeet -> True
    TyOpJoin -> True
    TyOpInterval -> True
    _        -> False

coeffectResourceAlgebraOps :: TypeOperator -> Bool
coeffectResourceAlgebraOps =
  \case
    TyOpPlus -> True
    TyOpTimes -> True
    TyOpMeet -> True
    TyOpJoin -> True
    TyOpInterval -> True
    _ -> False

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
    TyOpInterval -> (tyVar "k", tyVar "k", tyVar "k")

dataTypes :: [DataDecl]
dataTypes =
    -- Special built-in for products (which cannot be parsed)
    [ DataDecl
      { dataDeclSpan = nullSpanBuiltin
      , dataDeclId   = mkId ","
      , dataDeclTyVarCtxt = [((mkId "a"), Type 0),((mkId "b"), Type 0)]
      , dataDeclKindAnn = Just (Type 0)
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
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Int"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Float"))
        , funTy (TyCon $ mkId "DFloat") (funTy (TyCon $ mkId "DFloat") (TyCon $ mkId "DFloat"))]
    OpMinus ->
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Int"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Float"))
        , funTy (TyCon $ mkId "DFloat") (funTy (TyCon $ mkId "DFloat") (TyCon $ mkId "DFloat"))]
    OpTimes ->
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Int"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Float"))]
    OpDiv ->
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Int"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Float"))]
    OpEq ->
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))
        , funTy (TyCon $ mkId "DFloat") (funTy (TyCon $ mkId "DFloat") (TyCon $ mkId "DFloat"))]
    OpNotEq ->
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))
        , funTy (TyCon $ mkId "DFloat") (funTy (TyCon $ mkId "DFloat") (TyCon $ mkId "DFloat"))]
    OpLesserEq ->
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))
        , funTy (TyCon $ mkId "DFloat") (funTy (TyCon $ mkId "DFloat") (TyCon $ mkId "DFloat"))]
    OpLesser ->
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))
        , funTy (TyCon $ mkId "DFloat") (funTy (TyCon $ mkId "DFloat") (TyCon $ mkId "DFloat"))]
    OpGreater ->
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))
        , funTy (TyCon $ mkId "DFloat") (funTy (TyCon $ mkId "DFloat") (TyCon $ mkId "DFloat"))]
    OpGreaterEq ->
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))
        , funTy (TyCon $ mkId "DFloat") (funTy (TyCon $ mkId "DFloat") (TyCon $ mkId "DFloat"))]

-- TODO make a proper quasi quoter that parses this at compile time
builtinSrc :: String
builtinSrc = [r|

import Prelude

data () = ()

use : forall {a : Type} . a -> a [1]
use = BUILTIN

compose : forall a : Type, b : Type, c : Type
  . (b -> c) -> (a -> b) -> (a -> c)
compose g f = \x -> g (f x)

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

fromPure
  : forall {a : Type}
  . a <Pure> -> a
fromPure = BUILTIN

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
--Exceptions
--------------------------------------------------------------------------------

throw : forall {a : Type, k : Coeffect} . (a [0 : k]) <MayFail>
throw = BUILTIN

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
  . (LChan s -> ()) -> LChan (Dual s)
forkLinear = BUILTIN

send
  : forall {a : Type, s : Protocol}
  . LChan (Send a s) -> a -> LChan s
send = BUILTIN

recv
  : forall {a : Type, s : Protocol}
  . LChan (Recv a s) -> (a, LChan s)
recv = BUILTIN

close : LChan End -> ()
close = BUILTIN

gsend
  : forall {a : Type, s : Protocol}
  . Chan (Send a s) -> a -> (Chan s) <Session>
gsend = BUILTIN

grecv
  : forall {a : Type, s : Protocol}
  . Chan (Recv a s) -> (a, Chan s) <Session>
grecv = BUILTIN

gclose : Chan End -> () <Session>
gclose = BUILTIN

-- trace : String -> () <>
-- trace = BUILTIN

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

-- newPtr'
--   : forall { a : Type }
--   . a -> (exists id . ((Ptr id) [], Cap a id)
-- newPtr' = BUILTIN

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
      unDef (Def _ name _ _ (Forall _ bs cs t)) = (name, Forall nullSpanBuiltin bs cs t)
