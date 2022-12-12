-- Provides all the type information for built-ins

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}

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
import Language.Granule.Utils

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
--    * boolean flag on whether they are indexed types or not
typeConstructors :: (?globals :: Globals) => [(Id, (Type, [Id], Bool))]
typeConstructors =
  -- If we have the security levels extension turned on then include these things
  (extensionDependent [(SecurityLevels, [(mkId "Level",    (kcoeffect, [], False))
                                       , (mkId "Unused",   (tyCon "Level", [], False))
                                      , (mkId "Dunno",    (tyCon "Level", [], False))])] [])
 ++
  -- Everything else is always in scope
    [ (mkId "Coeffect",  (Type 0, [], False))
    , (mkId "Effect",    (Type 0, [], False))
    , (mkId "Guarantee", (Type 0, [], False))
    , (mkId "Predicate", (Type 0, [], False))
    , (mkId "->",     (funTy (Type 0) (funTy (Type 0) (Type 0)), [], False))
    , (mkId ",,",     (funTy kcoeffect (funTy kcoeffect kcoeffect), [mkId ",,"], False))
    , (mkId "ExactSemiring", (funTy (tyCon "Semiring") (tyCon "Predicate"), [], True))
    , (mkId "Int",    (Type 0, [], False))
    , (mkId "Float",  (Type 0, [], False))
    , (mkId "DFloat",  (Type 0, [], False)) -- special floats that can be tracked for sensitivty
    , (mkId "Char",   (Type 0, [], False))
    , (mkId "String", (Type 0, [], False))
    , (mkId "Inverse", ((funTy (Type 0) (Type 0)), [], False))
    -- Session type related things
    , (mkId "Protocol", (Type 0, [], False))
    , (mkId "SingleAction", ((funTy (tyCon "Protocol") (tyCon "Predicate")), [], True))
    , (mkId "ReceivePrefix", ((funTy (tyCon "Protocol") (tyCon "Predicate")), [], True))
    , (mkId "Sends", (funTy (tyCon "Nat") (funTy (tyCon "Protocol") (tyCon "Predicate")), [], True))
    , (mkId "Graded", (funTy (tyCon "Nat") (funTy (tyCon "Protocol") (tyCon "Protocol")), [], True))

    -- # Coeffect types
    , (mkId "Nat",      (kcoeffect, [], False))
    , (mkId "Q",        (kcoeffect, [], False)) -- Rationals
    , (mkId "OOZ",      (kcoeffect, [], False)) -- 1 + 1 = 0
    , (mkId "LNL",      (kcoeffect, [], False)) -- Linear vs Non-linear semiring
    -- LNL members
    , (mkId "Zero",     (tyCon "LNL", [], False))
    , (mkId "One",      (tyCon "LNL", [], False))
    , (mkId "Many",     (tyCon "LNL", [], False))
    -- Security levels
    
    -- Note that Private/Public can be members of Sec (and map to Hi/Lo) or if 'SecurityLevels' is
    -- turned on then they are part of the 'Level' semiring
    , (mkId "Private",  (extensionDependent [(SecurityLevels, tyCon "Level")] (tyCon "Sec"), [], False))
    , (mkId "Public",   (extensionDependent [(SecurityLevels, tyCon "Level")] (tyCon "Sec"), [], False))
    -- Alternate security levels (a la Gaboardi et al. 2016 and Abel-Bernardy 2020)
    , (mkId "Sec",  (kcoeffect, [], False))
    , (mkId "Hi",    (tyCon "Sec", [], False))
    , (mkId "Lo",    (tyCon "Sec", [], False))
    -- Uniqueness
    , (mkId "Uniqueness", (kguarantee, [], False))
    , (mkId "Unique", (tyCon "Uniqueness", [], False))
    -- Integrity
    , (mkId "Integrity", (kguarantee, [], False))
    , (mkId "Trusted", (tyCon "Integrity", [], False))
    -- Other coeffect constructors
    , (mkId "Interval", (kcoeffect .-> kcoeffect, [], False))
    -- Channels and protocol types
    , (mkId "Send", (funTy (Type 0) (funTy protocol protocol), [], False))
    , (mkId "Recv", (funTy (Type 0) (funTy protocol protocol), [], False))
    , (mkId "End" , (protocol, [], False))
    , (mkId "Select" , (funTy protocol (funTy protocol protocol), [], False))
    , (mkId "Offer" , (funTy protocol (funTy protocol protocol), [], False))
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
    , (mkId "IO",       (keffect, [], False))

    --Effect grade types - Exceptions
    , (mkId "Exception", (keffect, [], False))
    , (mkId "Success", (tyCon "Exception", [], False))
    , (mkId "MayFail", (tyCon "Exception", [], False))

    -- Arrays
    , (mkId "FloatArray", (Type 0, [], False))

    -- Capability related things
    , (mkId "CapabilityType", (funTy (tyCon "Capability") (Type 0), [], True))
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
    -- Special built-ins for products (which cannot be parsed)
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
    ] ++ [ DataDecl
      { dataDeclSpan = nullSpanBuiltin
      , dataDeclId   = mkId "&"
      , dataDeclTyVarCtxt = [((mkId "a"), Type 0),((mkId "b"), Type 0)]
      , dataDeclKindAnn = Just (Type 0)
      , dataDeclDataConstrs = [
        DataConstrNonIndexed
          { dataConstrSpan = nullSpanBuiltin
          , dataConstrId = mkId "&"
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
        , funTy (TyCon $ mkId "DFloat") (funTy (TyCon $ mkId "DFloat") (TyCon $ mkId "Bool"))]
    OpNotEq ->
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))
        , funTy (TyCon $ mkId "DFloat") (funTy (TyCon $ mkId "DFloat") (TyCon $ mkId "Bool"))]
    OpLesserEq ->
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))
        , funTy (TyCon $ mkId "DFloat") (funTy (TyCon $ mkId "DFloat") (TyCon $ mkId "Bool"))]
    OpLesser ->
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))
        , funTy (TyCon $ mkId "DFloat") (funTy (TyCon $ mkId "DFloat") (TyCon $ mkId "Bool"))]
    OpGreater ->
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))
        , funTy (TyCon $ mkId "DFloat") (funTy (TyCon $ mkId "DFloat") (TyCon $ mkId "Bool"))]
    OpGreaterEq ->
      funTy (TyCon $ mkId "Int") (funTy (TyCon $ mkId "Int") (TyCon $ mkId "Bool"))
      :| [funTy (TyCon $ mkId "Float") (funTy (TyCon $ mkId "Float") (TyCon $ mkId "Bool"))
        , funTy (TyCon $ mkId "DFloat") (funTy (TyCon $ mkId "DFloat") (TyCon $ mkId "Bool"))]

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
  . {SingleAction s, ExactSemiring k} => ((Chan s) [c] -> () <Session>) -> ((Chan (Dual s)) [c]) <Session>
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

selectLeft : forall {p1 p2 : Protocol}
          . LChan (Select p1 p2) -> LChan p1
selectLeft = BUILTIN

selectRight : forall {p1 p2 : Protocol}
            . LChan (Select p1 p2) -> LChan p2
selectRight = BUILTIN

offer : forall {p1 p2 : Protocol, a : Type}
      . (LChan p1 -> a) -> (LChan p2 -> a) -> LChan (Offer p1 p2) -> a
offer = BUILTIN

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

forkNonLinear : forall {p : Protocol, s : Semiring, r : s}
              . {SingleAction p, ExactSemiring s} => ((LChan p) [r] -> ()) -> (LChan (Dual p)) [r]
forkNonLinear = BUILTIN

forkMulticast : forall {p : Protocol, n : Nat}
              . {Sends p} => (LChan (Graded n p) -> ()) -> N n -> Vec n (LChan (Dual p))
forkMulticast = BUILTIN

forkReplicate : forall {p : Protocol, n : Nat} . {ReceivePrefix p}
              => (LChan p -> ()) [0..n] -> N n -> Vec n ((LChan (Dual p)) [0..1])
forkReplicate = BUILTIN

forkReplicateExactly : forall {p : Protocol, n : Nat} . {ReceivePrefix p}
                  => (LChan p -> ()) [n] ->  N n -> Vec n (LChan (Dual p))
forkReplicateExactly = BUILTIN

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

moveString : String -> String []
moveString = BUILTIN

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
  . *a -> !a
uniqueReturn = BUILTIN

uniqueBind
  : forall {a b : Type}
  . (*a -> !b) -> !a -> !b
uniqueBind = BUILTIN

uniquePush 
  : forall {a b : Type} 
  . *(a, b)  -> (*a, *b)
uniquePush = BUILTIN

uniquePull 
  : forall {a b : Type} 
  . (*a, *b) -> *(a, b)
uniquePull = BUILTIN

trustedReturn
  : forall {a : Type}
  . [Trusted] a -> a [Lo]
trustedReturn = BUILTIN

trustedBind
  : forall {a b : Type}
  . ([Trusted] a -> b [Lo]) -> a [Lo] -> b [Lo]
trustedBind = BUILTIN

--------------------------------------------------------------------------------
-- Mutable arrays
--------------------------------------------------------------------------------

newFloatArray : Int -> *FloatArray
newFloatArray = BUILTIN

newFloatArrayI : Int -> FloatArray
newFloatArrayI = BUILTIN

readFloatArray : *FloatArray -> Int -> (Float, *FloatArray)
readFloatArray = BUILTIN

readFloatArrayI : FloatArray -> Int -> (Float, FloatArray)
readFloatArrayI = BUILTIN

writeFloatArray : *FloatArray -> Int -> Float -> *FloatArray
writeFloatArray = BUILTIN

writeFloatArrayI : FloatArray -> Int -> Float -> FloatArray
writeFloatArrayI = BUILTIN

lengthFloatArray : *FloatArray -> (Int, *FloatArray)
lengthFloatArray = BUILTIN

lengthFloatArrayI : FloatArray -> (Int, FloatArray)
lengthFloatArrayI = BUILTIN

deleteFloatArray : *FloatArray -> ()
deleteFloatArray = BUILTIN

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

--------------------------------------------------------------------------------
-- Additive conjunction (linear logic)
--------------------------------------------------------------------------------

with : forall {a b : Type} . a [0..1] -> b [0..1] -> a & b
with = BUILTIN

projL : forall {a b : Type} . a & b -> a
projL = BUILTIN

projR : forall {a b : Type} . a & b -> b
projR = BUILTIN

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

-- List of primitives that can't be promoted in CBV
unpromotables :: [String]
unpromotables = ["newFloatArray", "forkLinear", "forkLinear'", "forkMulticast", "forkReplicate", "forkReplicateExactly"]

