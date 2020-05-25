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

kindConstructor :: [(Id, (Type (Succ One), [Id], Bool))]
kindConstructor =
  [ (mkId "Coeffect", (Type (LSucc LZero), [], False))
  , (mkId "Effect", (Type (LSucc LZero), [], False))
  , (mkId "Predicate", (Type (LSucc LZero), [], False)) ]

-- Associates type constuctors names to their:
--    * kind
--    * list of (finite) matchable constructor names (but not the actual set of constructor names which could be infinite)
--    * boolean flag on whether they are indexed types or not
typeConstructors :: [(Id, (TypeWithLevel, [Id], Bool))] -- TODO Cardinality is not a good term
typeConstructors =
    [ (mkId "->", (TypeWithLevel (LSucc LZero) $ funTy (Type LZero) (funTy (Type LZero) (Type LZero)), [], False))
    , (mkId "×", (TypeWithLevel (LSucc (LSucc LZero)) $ funTy (tyCon $ "Coeffect") (funTy (tyCon $ "Coeffect") (tyCon $ "Coeffect")), [mkId ","], False))
    , (mkId "Int",  (TypeWithLevel (LSucc LZero) $ Type LZero, [], False))
    , (mkId "Float", (TypeWithLevel (LSucc LZero) $ Type LZero, [], False))
    , (mkId "Char", (TypeWithLevel (LSucc LZero) $ Type LZero, [], False))
    , (mkId "String", (TypeWithLevel (LSucc LZero) $ Type LZero, [], False))
    , (mkId "Protocol", (TypeWithLevel (LSucc LZero) $ Type LZero, [], False))
    , (mkId "Nat",  (TypeWithLevel (LSucc (LSucc LZero)) $ KUnion (tyCon "Coeffect") (tyCon "Effect"), [], False))
    , (mkId "Q",    (TypeWithLevel (LSucc (LSucc LZero)) $ tyCon "Coeffect", [], False)) -- Rationals
    , (mkId "Level", (TypeWithLevel (LSucc (LSucc LZero)) $ tyCon "Coeffect", [], False)) -- Security level
    , (mkId "Private", (TypeWithLevel (LSucc LZero) $ tyCon "Level", [], False))
    , (mkId "Public", (TypeWithLevel (LSucc LZero) $ tyCon "Level", [], False))
    , (mkId "Unused", (TypeWithLevel (LSucc LZero) $ tyCon "Level", [], False))
    , (mkId "Interval", (TypeWithLevel (LSucc (LSucc LZero)) $ funTy (tyCon "Coeffect") (tyCon "Coeffect"), [], False))
    , (mkId "Set", (TypeWithLevel (LSucc (LSucc LZero)) $ funTy (TyVar $ mkId "k") (funTy (tyCon "k") (tyCon "Coeffect")), [], False))
    -- Channels and protocol types
    , (mkId "Send", (TypeWithLevel (LSucc LZero) $ funTy (Type LZero) (funTy protocol protocol), [], False))
    , (mkId "Recv", (TypeWithLevel (LSucc LZero) $ funTy (Type LZero) (funTy protocol protocol), [], False))
    , (mkId "End" , (TypeWithLevel (LSucc LZero) $ protocol, [], False))
    , (mkId "Chan", (TypeWithLevel (LSucc LZero) $ funTy protocol (Type LZero), [], True))
    , (mkId "Dual", (TypeWithLevel (LSucc LZero) $ funTy protocol protocol, [], True))
    , (mkId "->", (TypeWithLevel (LSucc LZero) $ funTy (Type LZero) (funTy (Type LZero) (Type LZero)), [], False))
    -- Top completion on a coeffect, e.g., Ext Nat is extended naturals (with ∞)
    , (mkId "Ext", (TypeWithLevel (LSucc (LSucc LZero)) $ funTy (tyCon "Coeffect") (tyCon "Coeffect"), [], True))
    -- Effect grade types - Sessions
    , (mkId "Session", (TypeWithLevel (LSucc LZero) $ TyCon $ mkId "Com", [], True))
    , (mkId "Com", (TypeWithLevel (LSucc (LSucc LZero)) $ (tyCon "Effect"), [], False))
    -- Effect grade types - IO
    , (mkId "IO", (TypeWithLevel (LSucc (LSucc LZero)) $ (tyCon "Effect"), [], False))
    , (mkId "Stdout", (TypeWithLevel (LSucc LZero) $ TyCon $ mkId "IOElem", [], False))
    , (mkId "Stdin", (TypeWithLevel (LSucc LZero) $ TyCon $ mkId "IOElem", [], False))
    , (mkId "Stderr", (TypeWithLevel (LSucc LZero) $ TyCon $ mkId "IOElem", [], False))
    , (mkId "Open", (TypeWithLevel (LSucc LZero) $ TyCon $ mkId "IOElem", [], False))
    , (mkId "Read", (TypeWithLevel (LSucc LZero) $ TyCon $ mkId "IOElem", [], False))
    , (mkId "Write", (TypeWithLevel (LSucc LZero) $ TyCon $ mkId "IOElem", [], False))
    , (mkId "IOExcept", (TypeWithLevel (LSucc LZero) $ TyCon $ mkId "IOElem", [], False))
    , (mkId "Close", (TypeWithLevel (LSucc LZero) $ TyCon $ mkId "IOElem", [], False))
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
    _        -> False

coeffectResourceAlgebraOps :: TypeOperator -> Bool
coeffectResourceAlgebraOps =
  \case
    TyOpPlus -> True
    TyOpTimes -> True
    TyOpMeet -> True
    TyOpJoin -> True
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
