-- Defines the 'Checker' monad used in the type checker
-- and various interfaces for working within this monad

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Checker.Environment where

import Checker.Coeffects
import Data.SBV
import Control.Monad.State.Strict
import qualified Control.Monad.Trans.Reader as MR
import Control.Monad.Reader.Class

import Syntax.Expr (Id, CKind)

-- State of the check/synth functions
data Checker a =
  Checker { unwrap :: MR.ReaderT [(Id, Id)] (StateT CheckerState IO) a }

evalChecker :: CheckerState -> [(Id, Id)] -> Checker a -> IO a
evalChecker initialState nameMap =
  flip evalStateT initialState . flip MR.runReaderT nameMap . unwrap

data CheckerState = CS
            { uniqueVarId  :: VarCounter
            , predicate    :: SolverInfo
            }

-- For fresh name generation
type VarCounter  = Int

-- Map from Ids to symbolic integer variables in the solver
type SolverVars  = [(Id, SCoeffect)]

-- Pair of a predicate and the id<->solver-variables map
type SolverInfo  = Symbolic (SBool, SolverVars)

-- Various interfaces for the checker

instance Monad Checker where
  return = Checker . return
  (Checker x) >>= f = Checker (x >>= (unwrap . f))

instance Functor Checker where
  fmap f (Checker x) = Checker (fmap f x)

instance Applicative Checker where
  pure    = return
  f <*> x = f >>= \f' -> x >>= \x' -> return (f' x')

instance MonadState CheckerState Checker where
  get = Checker get
  put s = Checker (put s)

instance MonadIO Checker where
  liftIO = Checker . lift . lift

instance MonadReader [(Id, Id)] Checker where
  ask = Checker $ MR.ask