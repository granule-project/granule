-- Defines the 'Checker' monad used in the type checker
-- and various interfaces for working within this monad

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Checker.Environment where

import Control.Monad.State.Strict

import Control.Monad.Trans.Maybe
import qualified Control.Monad.Trans.Reader as MR
import Control.Monad.Reader.Class

import Checker.Constraints (Constraint, Quantifier)
import Context
import Syntax.Expr (Id, CKind, Span, Type, Pattern)
import Syntax.Pretty

-- State of the check/synth functions
newtype Checker a =
  Checker { unwrap :: MR.ReaderT [(Id, Id)] (StateT CheckerState IO) a }

evalChecker :: CheckerState -> [(Id, Id)] -> Checker a -> IO a
evalChecker initialState nameMap =
  flip evalStateT initialState . flip MR.runReaderT nameMap . unwrap

runChecker :: CheckerState -> [(Id, Id)] -> Checker a -> IO (a, CheckerState)
runChecker initialState nameMap =
  flip runStateT initialState . flip MR.runReaderT nameMap . unwrap

-- For fresh name generation
type VarCounter  = Int

data CheckerState = CS
            { -- Fresh variable id
              uniqueVarId  :: VarCounter
            -- Conjunction of constraints
            , predicate    :: [Constraint]
            -- Coeffect environment, map coeffect vars to their kinds
            , ckenv        :: Env (CKind, Quantifier)
            -- Environment of resoled coeffect type variables
            -- (used just before solver, to resolve any type
            -- variables that appear in constraints)
            , cVarEnv   :: Env CKind
            }
  deriving Show -- for debugging

-- Generate a fresh alphanumeric variable name
freshVar :: String -> MaybeT Checker String
freshVar s = do
  checkerState <- get
  let v = uniqueVarId checkerState
  let prefix = s ++ "_" ++ ["a", "b", "c", "d"] !! (v `mod` 4)
  let cvar = prefix ++ show v
  put $ checkerState { uniqueVarId = v + 1 }
  return cvar

initState :: CheckerState
initState = CS 0 ground emptyEnv emptyEnv
  where
    ground   = []
    emptyEnv = []

-- | A helper for adding a constraint to the environment
addConstraint :: Constraint -> MaybeT Checker ()
addConstraint p = do
  checkerState <- get
  put $ checkerState { predicate = p : predicate checkerState }

-- | Stops the checker
halt :: MaybeT Checker a
halt = MaybeT (return Nothing)

-- | A helper for raising a type error
illTyped :: Span -> String -> MaybeT Checker a
illTyped = visibleError "Type" halt

illLinearity :: Span -> String -> MaybeT Checker a
illLinearity = visibleError "Linearity" halt

illGraded :: Span -> String -> MaybeT Checker ()
illGraded = visibleError "Grading" (return ())

illTypedPattern :: Span -> Type -> Pattern -> MaybeT Checker a
illTypedPattern s ty pat =
  visibleError "Pattern typing" halt s
    (pretty pat ++ " does not have type " ++ pretty ty)

-- | Helper for constructing error handlers
visibleError :: String -> MaybeT Checker a -> Span -> String -> MaybeT Checker a
visibleError kind next ((0, 0), (0, 0)) s =
  liftIO (putStrLn $ kind ++ " error: " ++ s) >> next

visibleError kind next ((sl, sc), (_, _)) s =
  liftIO (putStrLn $ show sl ++ ":" ++ show sc ++ ": " ++ kind ++ " error:\n\t"
                   ++ s) >> next


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
  ask = Checker MR.ask
  local r (Checker x) = Checker (MR.local r x)
