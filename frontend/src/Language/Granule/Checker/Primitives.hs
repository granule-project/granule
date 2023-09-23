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
    ,(mkId "Inverse", ([mkId "a"], FunTy Nothing Nothing (TyVar $ mkId "a") (TyCon $ mkId "()")))
    ,(mkId "Pushable", ([mkId "a"], TyInfix TyOpHsup (tyVar "a") (tyVar "a")))
    ]
  where
    ioElems = ["Stdout", "Stdin", "Stderr", "Open", "Read", "Write", "IOExcept", "Close"]

-- List of those things which are 'physical' resource (i.e., not dropable)
nonDropable :: [Id]
nonDropable = [mkId "Handle", mkId "LChan", mkId "Chan"]

capabilities :: [(Id, Type)]
capabilities =
   [(mkId "Console", funTy (tyCon "String") (tyCon "()"))
  , (mkId "TimeDate", funTy (tyCon "()") (tyCon "String"))]

overlapsAllowed :: [Id]
overlapsAllowed =
  [mkId "One", mkId "Private", mkId "Public", mkId "Unused", mkId "Set", mkId "SetOp"]

-- Associates type constuctors names to their:
--    * kind
--    * list of (finite) matchable constructor names (but not the actual set of constructor names which could be infinite)
--    * list of which type parameters are indices (proxy for whether they are indexed types or not)
typeConstructors :: (?globals :: Globals) => [(Id, (Type, [Id], [Int]))]
typeConstructors =
  -- If we have the security levels extension turned on then include these things
  (extensionDependent [(SecurityLevels, [(mkId "Level",    (kcoeffect, [], []))
                                       , (mkId "Unused",   (tyCon "Level", [], []))
                                       , (mkId "Dunno",    (tyCon "Level", [], []))])] [])
 ++
  -- Everything else is always in scope
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
    , (mkId "Inverse", ((funTy (Type 0) (Type 0)), [], []))
    -- Predicates on deriving operations:x
    , (mkId "Dropable", (funTy (Type 0) kpredicate, [], [0]))
    -- TODO: add deriving for this
    -- , (mkId "Moveable", (funTy (Type 0) kpredicate, [], [0]))
    -- Session type related things
    , (mkId "ExactSemiring", (funTy (tyCon "Semiring") (tyCon "Predicate"), [], []))
    , (mkId "Protocol", (Type 0, [], []))
    , (mkId "SingleAction", ((funTy (tyCon "Protocol") (tyCon "Predicate")), [], [0]))
    , (mkId "ReceivePrefix", ((funTy (tyCon "Protocol") (tyCon "Predicate")), [], [0]))
    , (mkId "Sends", (funTy (tyCon "Nat") (funTy (tyCon "Protocol") (tyCon "Predicate")), [], [0]))
    , (mkId "Graded", (funTy (tyCon "Nat") (funTy (tyCon "Protocol") (tyCon "Protocol")), [], [0]))

    -- # Coeffect types
    , (mkId "Nat",      (kcoeffect, [], []))
    , (mkId "Q",        (kcoeffect, [], [])) -- Rationals
    , (mkId "OOZ",      (kcoeffect, [], [])) -- 1 + 1 = 0
    , (mkId "LNL",      (kcoeffect, [], [])) -- Linear vs Non-linear semiring
    , (mkId "Set",      (funTy (Type 0) kcoeffect, [], [0]))
    , (mkId "SetOp",    (funTy (Type 0) kcoeffect, [], [0]))
    -- LNL members
    , (mkId "Zero",     (tyCon "LNL", [], []))
    , (mkId "One",      (tyCon "LNL", [], []))
    , (mkId "Many",     (tyCon "LNL", [], []))

    , (mkId "Cartesian", (kcoeffect, [], []))
    , (mkId "Any", (tyCon "Cartesian", [], []))
    -- Security levels

    -- Note that Private/Public can be members of Sec (and map to Hi/Lo) or if 'SecurityLevels' is
    -- turned on then they are part of the 'Level' semiring
    -- Security levels
    , (mkId "Private",  (extensionDependent [(SecurityLevels, tyCon "Level")] (tyCon "Sec"), [], []))
    , (mkId "Public",   (extensionDependent [(SecurityLevels, tyCon "Level")] (tyCon "Sec"), [], []))
    -- Alternate security levels (a la Gaboardi et al. 2016 and Abel-Bernardy 2020)
    , (mkId "Sec",  (kcoeffect, [], []))
    , (mkId "Hi",    (tyCon "Sec", [], []))
    , (mkId "Lo",    (tyCon "Sec", [], []))
    -- Uniqueness
    , (mkId "Uniqueness", (kguarantee, [], []))
    , (mkId "Unique", (tyCon "Uniqueness", [], []))
    -- Integrity
    , (mkId "Integrity", (kguarantee, [], []))
    , (mkId "Trusted", (tyCon "Integrity", [], []))
    -- Other coeffect constructors
    , (mkId "Interval", (kcoeffect .-> kcoeffect, [], []))
    -- Channels and protocol types
    , (mkId "Send", (funTy (Type 0) (funTy protocol protocol), [], []))
    , (mkId "Recv", (funTy (Type 0) (funTy protocol protocol), [], []))
    , (mkId "End" , (protocol, [], []))
    , (mkId "Select" , (funTy protocol (funTy protocol protocol), [], []))
    , (mkId "Offer" , (funTy protocol (funTy protocol protocol), [], []))
    , (mkId "Chan", (funTy protocol (Type 0), [], [0]))
    , (mkId "LChan", (funTy protocol (Type 0), [], [0]))
    , (mkId "Dual", (funTy protocol protocol, [], [0]))
    -- Top completion on a coeffect, e.g., Ext Nat is extended naturals (with ∞)
    , (mkId "Ext", (funTy kcoeffect kcoeffect, [], [0]))
    -- Effect grade types - Sessions
    , (mkId "Session",  (tyCon "Com", [], []))
    , (mkId "Com",      (keffect, [], []))
    -- Effect grade types - IO
    , (mkId "IO",       (keffect, [], []))

    --Effect grade types - Exceptions
    , (mkId "Exception", (keffect, [], []))
    , (mkId "Success", (tyCon "Exception", [], []))
    , (mkId "MayFail", (tyCon "Exception", [], []))

     -- Free : (e : Type) -> Effect
    , (mkId "Free", (FunTy (Just $ mkId "eff") (Type 0)
                       (FunTy Nothing (funTy (Type 0) (funTy (tyVar "eff") (Type 0))) keffect), [], True))
    , (mkId "Eff", 
         (FunTy (Just $ mkId "eff") (Type 0)
            (FunTy (Just $ mkId "sig") (funTy (Type 0) (funTy (tyVar "eff") (Type 0)))
              (funTy (TyApp (tyCon "Set") (tyVar "eff")) (TyApp (TyApp (tyCon "Free") (tyVar "eff")) (tyVar "sig")))), [], True))

    -- Arrays
    , (mkId "FloatArray", (Type 0, [], []))

    -- Capability related things
    , (mkId "CapabilityType", (funTy (tyCon "Capability") (Type 0), [], [0]))
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
    TyOpImpl     -> True
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
    TyOpLesserNat -> (kNat, kNat, kpredicate)
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
    TyOpImpl    -> (kpredicate, kpredicate, kpredicate)
    TyOpHsup    -> (tyVar "k", tyVar "k", kpredicate)

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
builtinSrc = [r|------
--- Module: Primitives
--- Description: Built-in primitive definitions
------

import Prelude

--- # Core linear functional combinators

--- Unit type
data () = ()

--- Allows a linear variable to be promoted to a graded modality
--- specifying an exact usage of 1
use : forall {a : Type} . a -> a [1]
use = BUILTIN

--- Linear function composition
compose : forall {a : Type, b : Type, c : Type}
  . (b -> c) -> (a -> b) -> (a -> c)
compose = BUILTIN
-- Defined in the interpreter as \g -> \f -> \x -> g (f x)

--------------------------------------------------------------------------------
--- # Arithmetic
--------------------------------------------------------------------------------

--- Integer division
div : Int -> Int -> Int
div = BUILTIN

--------------------------------------------------------------------------------
--- # Graded Possiblity
--------------------------------------------------------------------------------

--- Inject into a computation for any graded monad
pure
  : forall {a : Type}
  . a -> a <>
pure = BUILTIN

--- Extract form a pure computation
fromPure
  : forall {a : Type}
  . a <Pure> -> a
fromPure = BUILTIN

-- Generic effect
call : forall {i : Type, o : Type, r : Type, labels : Type, sigs : Type -> labels -> Type, e : labels} 
   . (i -> (o -> r) -> sigs r e) -> i -> o <Eff labels sigs {e}>
call = BUILTIN

--------------------------------------------------------------------------------
--- # I/O
--------------------------------------------------------------------------------

--- IO effect operation information

data IOElem = Stdout | Stdin | Stderr | Open | Read | Write | IOExcept | Close

--- Read from standard input
fromStdin : String <{Stdin}>
fromStdin = BUILTIN

--- Write to standard output
toStdout : String -> () <{Stdout}>
toStdout = BUILTIN

--- Write to standard output
toStderr : String -> () <{Stderr}>
toStderr = BUILTIN

--------------------------------------------------------------------------------
--- # Exceptions
--------------------------------------------------------------------------------

throw : forall {a : Type, k : Coeffect} . (a [0 : k]) <MayFail>
throw = BUILTIN

--------------------------------------------------------------------------------
--- # Conversions
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
--- # Concurrency and Session Types
--------------------------------------------------------------------------------


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

selectLeft : forall {p1 p2 : Protocol}
          . LChan (Select p1 p2) -> LChan p1
selectLeft = BUILTIN

selectRight : forall {p1 p2 : Protocol}
            . LChan (Select p1 p2) -> LChan p2
selectRight = BUILTIN

offer : forall {p1 p2 : Protocol, a : Type}
      . (LChan p1 -> a) -> (LChan p2 -> a) -> LChan (Offer p1 p2) -> a
offer = BUILTIN

--------------------------------------------------------------------------------
--- # Non-linear communication and concurrency patterns
--------------------------------------------------------------------------------

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

---------------------------------
--- # Concurrency primitives using side effects
----------------------------------

fork
  : forall {s : Protocol, k : Coeffect, c : k}
  . {SingleAction s, ExactSemiring k} => ((Chan s) [c] -> () <Session>) -> ((Chan (Dual s)) [c]) <Session>
fork = BUILTIN

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

--------------------------------------------------------------------------------
--- # File Handles
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
--- # Char
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
--- # String manipulation
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

-- data
--   ArrayStack
--     (capacity : Nat)
--     (maxIndex : Nat)
--     (a : Type)
--   where

-- push
--   : ∀ {a : Type, cap : Nat, maxIndex : Nat}
--   . {maxIndex < cap}
--   ⇒ ArrayStack cap maxIndex a
--   → a
--   → ArrayStack cap (maxIndex + 1) a
-- push = BUILTIN

-- pop
--   : ∀ {a : Type, cap : Nat, maxIndex : Nat}
--   . {maxIndex > 0}
--   ⇒ ArrayStack cap maxIndex a
--   → a × ArrayStack cap (maxIndex - 1) a
-- pop = BUILTIN

-- -- Boxed array, so we allocate cap words
-- allocate
--   : ∀ {a : Type, cap : Nat}
--   . N cap
--   → ArrayStack cap 0 a
-- allocate = BUILTIN

-- swap
--   : ∀ {a : Type, cap : Nat, maxIndex : Nat}
--   . ArrayStack cap (maxIndex + 1) a
--   → Fin (maxIndex + 1)
--   → a
--   → a × ArrayStack cap (maxIndex + 1) a
-- swap = BUILTIN

-- copyArray
--   : ∀ {a : Type, cap : Nat, maxIndex : Nat}
--   . ArrayStack cap maxIndex (a [2])
--   → ArrayStack cap maxIndex a × ArrayStack cap maxIndex a
-- copyArray = BUILTIN

--------------------------------------------------------------------------------
--- # Cost
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
--- # Uniqueness modality
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

reveal
  : forall {a : Type}
  . a *{Trusted} -> a [Lo]
reveal = BUILTIN

trustedBind
  : forall {a b : Type}
  . (a *{Trusted} -> b [Lo]) -> a [Lo] -> b [Lo]
trustedBind = BUILTIN

--------------------------------------------------------------------------------
--- # Mutable array operations
--------------------------------------------------------------------------------

newFloatArray : Int -> *FloatArray
newFloatArray = BUILTIN

readFloatArray : *FloatArray -> Int -> (Float, *FloatArray)
readFloatArray = BUILTIN

writeFloatArray : *FloatArray -> Int -> Float -> *FloatArray
writeFloatArray = BUILTIN

lengthFloatArray : *FloatArray -> (Int, *FloatArray)
lengthFloatArray = BUILTIN

deleteFloatArray : *FloatArray -> ()
deleteFloatArray = BUILTIN

--------------------------------------------------------------------------------
--- # Imuutable array operations
--------------------------------------------------------------------------------

newFloatArrayI : Int -> FloatArray
newFloatArrayI = BUILTIN

readFloatArrayI : FloatArray -> Int -> (Float, FloatArray)
readFloatArrayI = BUILTIN

writeFloatArrayI : FloatArray -> Int -> Float -> FloatArray
writeFloatArrayI = BUILTIN

lengthFloatArrayI : FloatArray -> (Int, FloatArray)
lengthFloatArrayI = BUILTIN

--------------------------------------------------------------------------------
--- # Benchmarking
--------------------------------------------------------------------------------

data BenchList where BenchGroup String BenchList BenchList ; Bench Int String (Int [] -> () <{Stdout}>) BenchList; Done

mkIOBenchMain : BenchList -> () <>
mkIOBenchMain = BUILTIN

---------------------
--- # Sensitivity
---------------------

scale : (k : Float) -> DFloat [k] -> DFloat
scale = BUILTIN

--------------------------------------------------------------------------------
--- # Capabilities
--------------------------------------------------------------------------------

data Capability = Console | TimeDate

cap : (c : Capability) -> () [{c}] -> CapabilityType c
cap = BUILTIN

--------------------------------------------------------------------------------
-- Additive conjunction (linear logic)
--------------------------------------------------------------------------------

-- with : forall {a b : Type} . a [0..1] -> b [0..1] -> a & b
-- with = BUILTIN

-- projL : forall {a b : Type} . a & b -> a
-- projL = BUILTIN

-- projR : forall {a b : Type} . a & b -> b
-- projR = BUILTIN

-- trace : String -> () <>
-- trace = BUILTIN

|]


builtinsParsed :: AST () ()
builtinsParsed = case parseDefs "builtins" builtinSrc of
        Right (ast, _) -> ast
        Left err -> error err

builtinDataTypesParsed :: [DataDecl]
builtins :: [(Id, TypeScheme)]
(builtinDataTypesParsed, builtins) =
  (types, map unDef defs)
    where
      AST types defs _ _ _ = builtinsParsed

      unDef :: Def () () -> (Id, TypeScheme)
      unDef (Def _ name _ _ _ (Forall _ bs cs t)) = (name, Forall nullSpanBuiltin bs cs t)

-- List of primitives that can't be promoted in CBV
unpromotables :: [String]
unpromotables = ["newFloatArray", "forkLinear", "forkMulticast", "forkReplicate", "forkReplicateExactly"]

