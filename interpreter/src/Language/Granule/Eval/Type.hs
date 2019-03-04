{- |
Module      :  Language.Granule.Eval.Type
Description :  The Evaluator Monad
Copyright   :  (c) 2019 Ben Moon

This module defines the 'Evaluator' monad, along with
various helpers for use in the interpreter.
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.Granule.Eval.Type
    (
    -- ** The Evaluator Monad
      Evaluator

    -- *** Running the evaluator
    , execEvaluator
    , initStateWithContext
    , runWithContext

    -- *** Retrieving information from the state
    , getCurrentContext
    , lookupInCurrentContext
    , lookupInDefMap

    -- *** Manipulating the state
    , buildDefMap
    , putContext

    -- *** IO inside the Evaluator
    , flushStdout
    , writeStr
    , runIOAction

    -- ** Runtime types
    , RExpr
    , RValue
    , Runtime(..)
    , runPrimitive
    , toRuntimeRep
    ) where


import Control.Monad.Fail (MonadFail)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState, StateT, evalStateT, get, modify')
import qualified Control.Concurrent.Chan as CC (Chan)
import qualified System.IO as SIO (Handle, hFlush, stdout)

import Language.Granule.Context (Ctxt)
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers (Id)
import Language.Granule.Syntax.Pretty (Pretty, prettyL)


---------------------------
----- Evaluator Monad -----
---------------------------


---------------------
-- Evaluator State --
---------------------


type DefMap = Ctxt RuntimeDef


data EvalState = EvalState {
      currentContext :: Ctxt RValue
    , tlds :: DefMap
    }


initState :: EvalState
initState = EvalState [] []


initStateWithContext :: Ctxt RValue -> EvalState
initStateWithContext ctxt = initState { currentContext = ctxt }


--------------------
-- Evaluator Type --
--------------------


newtype Evaluator a = Evaluator { unEvaluator :: StateT EvalState IO a }
    deriving (Functor, Applicative, Monad,
              MonadState EvalState,
              MonadIO, MonadFail)


execEvaluator :: Evaluator a -> EvalState -> IO a
execEvaluator = evalStateT . unEvaluator


execChild :: Evaluator a -> Evaluator (IO a)
execChild e = do
  st <- get
  pure $ execEvaluator e st


runWithContext :: Ctxt RValue -> Evaluator a -> IO a
runWithContext c r = execEvaluator r $ initStateWithContext c


-------------
-- Helpers --
-------------


buildDefMap :: [RuntimeDef] -> Evaluator ()
buildDefMap des =
  let dmap = foldr (\d@(Def _ n _ _) acc -> (n, d) : acc) [] des
  in putDefMap dmap


putDefMap :: DefMap -> Evaluator ()
putDefMap dmap = modify' $ \s -> s { tlds = dmap }


getDefMap :: Evaluator DefMap
getDefMap = fmap tlds get


lookupInDefMap :: Id -> Evaluator (Maybe RuntimeDef)
lookupInDefMap n = fmap (lookup n) getDefMap


getCurrentContext :: Evaluator (Ctxt RValue)
getCurrentContext = fmap currentContext get


putContext :: Ctxt RValue -> Evaluator ()
putContext c = modify' $ \s -> s { currentContext = c }


lookupInCurrentContext :: Id -> Evaluator (Maybe RValue)
lookupInCurrentContext n = fmap (lookup n) getCurrentContext


--------
-- IO --
--------


writeStr :: String -> Evaluator ()
writeStr = liftIO . putStr


flushStdout :: Evaluator ()
flushStdout = liftIO $ SIO.hFlush SIO.stdout


runPrimitive :: (RValue -> IO a) -> RValue -> Evaluator a
runPrimitive f = liftIO . f


-- | Execute an IO action inside of an Evaluator.
runInnerIO :: Evaluator (IO a) -> Evaluator a
runInnerIO e = do
  action <- e
  liftIO action


-- | Run an IO function inside an Evaluator.
runIOAction :: (IO a -> IO b) -> Evaluator a -> Evaluator b
runIOAction f e = runInnerIO (fmap f (execChild e))


-------------------------
----- Runtime Types -----
-------------------------


type RuntimeDef = Def (Runtime ()) ()


type RValue = Value (Runtime ()) ()


type RExpr = Expr (Runtime ()) ()


-- | Runtime values only used in the interpreter.
data Runtime a =
  -- | Primitive functions (builtins).
    Primitive ((Value (Runtime a) a) -> IO (Value (Runtime a) a))
  -- | Primitive operations that also close over the context.
  | PrimitiveClosure (Ctxt (Value (Runtime a) a) -> (Value (Runtime a) a) -> IO (Value (Runtime a) a))
  -- | File handler.
  | Handle SIO.Handle
  -- | Channels.
  | Chan (CC.Chan (Value (Runtime a) a))


instance Show (Runtime a) where
  show (Chan _)             = "Some channel"
  show (Primitive _)        = "Some primitive"
  show (PrimitiveClosure _) = "Some primitive closure"
  show (Handle _)           = "Some handle"


instance Show (Runtime a) => Pretty (Runtime a) where
  prettyL _ = show


----------------------------------
-- Runtime Representation Class --
----------------------------------


-- | Map an AST from the parser into the interpreter
-- | version with runtime values.
class RuntimeRep t where
  toRuntimeRep :: t () () -> t (Runtime ()) ()


instance RuntimeRep Def where
  toRuntimeRep (Def s i eqs tys) = Def s i (map toRuntimeRep eqs) tys


instance RuntimeRep Equation where
  toRuntimeRep (Equation s a ps e) = Equation s a ps (toRuntimeRep e)


instance RuntimeRep Expr where
  toRuntimeRep (Val s a v) = Val s a (toRuntimeRep v)
  toRuntimeRep (App s a e1 e2) =
      App s a (toRuntimeRep e1) (toRuntimeRep e2)
  toRuntimeRep (Binop s a o e1 e2) =
      Binop s a o (toRuntimeRep e1) (toRuntimeRep e2)
  toRuntimeRep (LetDiamond s a p t e1 e2) =
      LetDiamond s a p t (toRuntimeRep e1) (toRuntimeRep e2)
  toRuntimeRep (Case s a e ps) =
      Case s a (toRuntimeRep e) (map (\(p, e') -> (p, toRuntimeRep e')) ps)


instance RuntimeRep Value where
  toRuntimeRep (Ext _ ()) =
      error "Bug: Parser generated an extended value case when it shouldn't have"
  toRuntimeRep (Abs a p t e)   = Abs a p t (toRuntimeRep e)
  toRuntimeRep (Promote a e)   = Promote a (toRuntimeRep e)
  toRuntimeRep (Pure a e)      = Pure a (toRuntimeRep e)
  toRuntimeRep (Constr a i vs) = Constr a i (map toRuntimeRep vs)
  -- identity cases
  toRuntimeRep (CharLiteral c)   = CharLiteral c
  toRuntimeRep (StringLiteral c) = StringLiteral c
  toRuntimeRep (Var a x)         = Var a x
  toRuntimeRep (NumInt x)        = NumInt x
  toRuntimeRep (NumFloat x)      = NumFloat x
