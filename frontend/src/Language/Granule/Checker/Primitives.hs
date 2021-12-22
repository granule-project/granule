-- Provides all the type information for built-ins
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}

-- | Primitive data types and type constructors
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

-- A list of type alias as Id -> ([Tyvar], Type) pairs
typeAliases :: [(Id, ([Id], Type))]
typeAliases =
    -- IO = {p | p in IOElem}
    [(mkId "IO", ([], TySet Normal (map tyCon ioElems)))
    ,(mkId "Inverse", ([mkId "a"], FunTy Nothing (TyVar $ mkId "a") (TyCon $ mkId "()")))]
  where
    ioElems = ["Stdout", "Stdin", "Stderr", "Open", "Read", "Write", "IOExcept", "Close"]

capabilities :: [(Id, Type)]
capabilities =
   [(mkId "Console", funTy (tyCon "String") (tyCon "()"))
  , (mkId "TimeDate", funTy (tyCon "()") (tyCon "String"))]

-- Associates type constuctors names to their:
--    * kind
--    * list of (finite) matchable constructor names (but not the actual set of constructor names which could be infinite)
--    * list of which type parameters are indices (proxy for whether they are indexed types or not)
typeConstructors :: [(Id, (Type, [Id], [Int]))]
typeConstructors =
    [ (mkId "Coeffect",  (Type 2, [], []))
    , (mkId "Effect",    (Type 2, [], []))
    , (mkId "Guarantee", (Type 2, [], []))
    , (mkId "Predicate", (Type 2, [], []))
    , (mkId "->",     (funTy (Type 0) (funTy (Type 0) (Type 0)), [], []))
    , (mkId ",,",     (funTy kcoeffect (funTy kcoeffect kcoeffect), [mkId ",,"], []))
    , (mkId "Int",    (Type 0, [], []))
    , (mkId "Float",  (Type 0, [], []))
    , (mkId "DFloat",  (Type 0, [], [])) -- special floats that can be tracked for sensitivty
    , (mkId "Char",   (Type 0, [], []))
    , (mkId "String", (Type 0, [], []))
    , (mkId "Protocol", (Type 0, [], []))
    , (mkId "Inverse", ((funTy (Type 0) (Type 0)), [], []))
    -- # Coeffect types
    , (mkId "Nat",      (kcoeffect, [], []))
    , (mkId "Q",        (kcoeffect, [], [])) -- Rationals
    , (mkId "OOZ",      (kcoeffect, [], [])) -- 1 + 1 = 0
    , (mkId "LNL",      (kcoeffect, [], [])) -- Linear vs Non-linear semiring
    -- LNL members
    , (mkId "Zero",     (tyCon "LNL", [], []))
    , (mkId "One",      (tyCon "LNL", [], []))
    , (mkId "Many",     (tyCon "LNL", [], []))
    -- Borrowing
    , (mkId "Borrowing", (kcoeffect, [], []))
    , (mkId "One",       (tyCon "Borrowing", [], []))
    , (mkId "Beta",      (tyCon "Borrowing", [], []))
    , (mkId "Omega",     (tyCon "Borrowing", [], []))
    -- Security levels
    , (mkId "Level",    (kcoeffect, [], [])) -- Security level
    , (mkId "Private",  (tyCon "Level", [], []))
    , (mkId "Public",   (tyCon "Level", [], []))
    , (mkId "Unused",   (tyCon "Level", [], []))
    , (mkId "Dunno",    (tyCon "Level", [], []))
    -- Alternate security levels (a la Gaboardi et al. 2016 and Abel-Bernardy 2020)
    , (mkId "Sec",  (kcoeffect, [], []))
    , (mkId "Hi",    (tyCon "Sec", [], []))
    , (mkId "Lo",    (tyCon "Sec", [], []))
    -- Uniqueness
    , (mkId "Uniqueness", (kguarantee, [], []))
    , (mkId "Unique", (tyCon "Uniqueness", [], []))
    -- Other coeffect constructors
    , (mkId "Interval", (kcoeffect .-> kcoeffect, [], []))
    -- Channels and protocol types
    , (mkId "Send", (funTy (Type 0) (funTy protocol protocol), [], []))
    , (mkId "Recv", (funTy (Type 0) (funTy protocol protocol), [], []))
    , (mkId "End" , (protocol, [], []))
    , (mkId "Chan", (funTy protocol (Type 0), [], [0]))
    , (mkId "LChan", (funTy protocol (Type 0), [], [0]))
    , (mkId "Dual", (funTy protocol protocol, [], [0]))
    , (mkId "->", (funTy (Type 0) (funTy (Type 0) (Type 0)), [], []))
    -- Top completion on a coeffect, e.g., Ext Nat is extended naturals (with ∞)
    , (mkId "Ext", (funTy kcoeffect kcoeffect, [], [1]))
    -- Effect grade types - Sessions
    , (mkId "Session",  (tyCon "Com", [], []))
    , (mkId "Com",      (keffect, [], []))
    -- Effect grade types - IO
    , (mkId "IO",       (keffect, [], []))

    --Effect grade types - Exceptions
    , (mkId "Exception", (keffect, [], []))
    , (mkId "Success", (tyCon "Exception", [], []))
    , (mkId "MayFail", (tyCon "Exception", [], []))

    -- Arrays
<<<<<<< HEAD
    , (mkId "FloatArray", (Type 0, [], []))
=======
    , (mkId "FloatArray", (Type 0, [], False))

    -- Capability related things
    , (mkId "CapabilityType", (funTy (tyCon "Capability") (Type 0), [], True))
>>>>>>> eb3d002a (new feature, extending set coeffects, providing capability tracking)
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
    TyOpConverge -> True
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
    TyOpLesserNat -> (kNat, kNat, (TyCon (mkId "Predicate")))
    TyOpLesserEqNat -> (kNat, kNat, (TyCon (mkId "Predicate")))
    TyOpLesserEq -> (tyVar "k", tyVar "k", (TyCon (mkId "Predicate")))
    TyOpGreaterNat -> (kNat, kNat, (TyCon (mkId "Predicate")))
    TyOpGreaterEq -> (tyVar "k", tyVar "k", (TyCon (mkId "Predicate")))
    TyOpGreaterEqNat -> (kNat, kNat, (TyCon (mkId "Predicate")))
    TyOpEq -> (kNat, kNat, (TyCon (mkId "Predicate")))
    TyOpNotEq -> (kNat, kNat, (TyCon (mkId "Predicate")))
    TyOpPlus -> (kNat, kNat, kNat)
    TyOpTimes -> (kNat, kNat, kNat)
    TyOpMinus -> (kNat, kNat, kNat)
    TyOpExpon -> (kNat, kNat, kNat)
    TyOpMeet -> (kNat, kNat, kNat)
    TyOpJoin -> (kNat, kNat, kNat)
    TyOpInterval -> (tyVar "k", tyVar "k", tyVar "k")
    TyOpConverge -> (kNat, kNat, kNat)

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
        , funTy (TyCon $ mkId "Char") (funTy (TyCon $ mkId "Char") (TyCon $ mkId "Bool"))
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

compose : forall {a : Type, b : Type, c : Type}
  . (b -> c) -> (a -> b) -> (a -> c)
compose = BUILTIN
-- Defined in the interpreter as \g -> \f -> \x -> g (f x)

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

data IOElem = Stdout | Stdin | Stderr | Open | Read | Write | IOExcept | Close

fromStdin : String <{Stdin}>
fromStdin = BUILTIN

toStdout : String -> () <{Stdout}>
toStdout = BUILTIN

toStderr : String -> () <{Stderr}>
toStderr = BUILTIN

--------------------------------------------------------------------------------
-- Exceptions
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

showFloat : Float -> String
showFloat = BUILTIN

readInt : String -> Int
readInt = BUILTIN

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

forkLinear'
  : forall {p : Protocol, s : Semiring}
  . ((LChan p) [1 : s] -> ()) -> LChan (Dual p)
forkLinear' = BUILTIN

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

-- Moves

moveChar : Char -> Char []
moveChar = BUILTIN

moveInt : Int -> Int []
moveInt = BUILTIN


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

moveString : String -> String []
moveString = BUILTIN

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

copyArray
  : ∀ {a : Type, cap : Nat, maxIndex : Nat}
  . ArrayStack cap maxIndex (a [2])
  → ArrayStack cap maxIndex a × ArrayStack cap maxIndex a
copyArray = BUILTIN

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

--------------------------------------------------------------------------------
-- Uniqueness monadic operations
--------------------------------------------------------------------------------

uniqueReturn
  : forall {a : Type}
  . a *[Unique] -> a [Many]
uniqueReturn = BUILTIN

uniqueBind
  : forall {a b : Type}
  . (a *[Unique] -> b [Many]) -> a [Many] -> b [Many]
uniqueBind = BUILTIN

uniquePush 
  : forall {a b : Type} 
  . (a, b) *[Unique] -> (a *[Unique], b *[Unique])
uniquePush = BUILTIN

uniquePull 
  : forall {a b : Type} 
  . (a *[Unique], b *[Unique]) -> (a, b) *[Unique]
uniquePull = BUILTIN

--------------------------------------------------------------------------------
-- Mutable arrays
--------------------------------------------------------------------------------

newFloatArray : Int -> FloatArray *[Unique]
newFloatArray = BUILTIN

newFloatArray' : Int -> FloatArray
newFloatArray' = BUILTIN

readFloatArray : FloatArray *[Unique] -> Int -> (Float, FloatArray *[Unique])
readFloatArray = BUILTIN

readFloatArray' : FloatArray -> Int -> (Float, FloatArray)
readFloatArray' = BUILTIN

writeFloatArray : FloatArray *[Unique] -> Int -> Float -> FloatArray *[Unique]
writeFloatArray = BUILTIN

writeFloatArray' : FloatArray -> Int -> Float -> FloatArray
writeFloatArray' = BUILTIN

lengthFloatArray : FloatArray *[Unique] -> (Int, FloatArray *[Unique])
lengthFloatArray = BUILTIN

lengthFloatArray' : FloatArray -> (Int, FloatArray)
lengthFloatArray' = BUILTIN

deleteFloatArray : FloatArray *[Unique] -> ()
deleteFloatArray = BUILTIN

---------------------

scale : (k : Float) -> DFloat [k] -> DFloat
scale = BUILTIN
--------------------------------------------------------------------------------
-- Benchmarking
--------------------------------------------------------------------------------

data BenchList where BenchGroup String BenchList BenchList ; Bench Int String (Int [] -> () <{Stdout}>) BenchList; Done

mkIOBenchMain : BenchList -> () <>
mkIOBenchMain = BUILTIN

---------------------

scale : (k : Float) -> DFloat [k] -> DFloat
scale = BUILTIN


--------------------------------------------------------------------------------
-- Capabilities
--------------------------------------------------------------------------------

data Capability = Console | TimeDate

cap : (c : Capability) -> () [{c}] -> CapabilityType c
cap = BUILTIN

|]


builtinDataTypesParsed :: [DataDecl]
builtins :: [(Id, TypeScheme)]
(builtinDataTypesParsed, builtins) =
  (types, map unDef defs)
    where
      AST types defs _ _ _ = case parseDefs "builtins" builtinSrc of
        Right (ast, _) -> ast
        Left err -> error err

      unDef :: Def () () -> (Id, TypeScheme)
      unDef (Def _ name _ _ (Forall _ bs cs t)) = (name, Forall nullSpanBuiltin bs cs t)
