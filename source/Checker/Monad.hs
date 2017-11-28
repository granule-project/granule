-- Defines the 'Checker' monad used in the type checker
-- and various interfaces for working within this monad

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Checker.Monad where

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Trans.Reader as MR
import Control.Monad.Reader.Class
import System.IO (hPutStrLn, stderr)

import Checker.LaTeX
import Checker.Constraints
import Context
import Syntax.Expr (Id, CKind, Span, Type, Coeffect, Pattern)
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

-- Types or discharged coeffects
data Assumption =
    Linear Type
  | Discharged Type Coeffect

data CheckerState = CS
            { -- Fresh variable id
              uniqueVarId  :: VarCounter
            -- Predicate giving constraints
            , predicate      :: Pred
            -- Local stack of constraints (can be used to build implications)
            , predicateStack :: [Pred]
            -- Coeffect context, map coeffect vars to their kinds
            , ckctxt        :: Ctxt (CKind, Quantifier)
            -- Context of resoled coeffect type variables
            -- (used just before solver, to resolve any type
            -- variables that appear in constraints)
            , cVarCtxt   :: Ctxt CKind
            -- LaTeX derivation
            , deriv      :: Maybe Derivation
            , derivStack :: [Derivation]
            }
  deriving Show -- for debugging

-- *** Various helpers for manipulating the context

-- | Initial checker context state
initState :: CheckerState
initState = CS 0 ground [] emptyCtxt emptyCtxt Nothing []
  where
    ground   = Conj []
    emptyCtxt = []

-- | Helper for creating a few (existential) coeffect variable of a particular
--   coeffect type.
freshCoeffectVar :: Id -> CKind -> MaybeT Checker Id
freshCoeffectVar cvar kind = do
    cvar' <- freshVar cvar
    registerCoeffectVar cvar' kind ExistsQ
    return cvar'

-- | Helper for registering a new coeffect variable in the checker
registerCoeffectVar :: Id -> CKind -> Quantifier -> MaybeT Checker ()
registerCoeffectVar v k q = modify (\st -> st { ckctxt = (v, (k, q)) : ckctxt st })

-- | Start a new conjunction frame on the predicate stack
newConjunct :: MaybeT Checker ()
newConjunct = do
  checkerState <- get
  put (checkerState { predicateStack = Conj [] : predicateStack checkerState })

-- | Takes the top two conjunction frames and turns them into an impliciation
concludeImplication :: MaybeT Checker ()
concludeImplication = do
  checkerState <- get
  case predicateStack checkerState of
    (p' : p : stack) ->
      put (checkerState { predicateStack = Impl p p' : stack })
    _ -> error "Predicate: not enough conjunctions on the stack"

-- | A helper for adding a constraint to the context
addConstraint :: Constraint -> MaybeT Checker ()
addConstraint p = do
  checkerState <- get
  case predicateStack checkerState of
    (Conj ps : stack) ->
      put (checkerState { predicateStack = Conj (Con p : ps) : stack })
    stack ->
      put (checkerState { predicateStack = Conj [Con p] : stack })

-- | Generate a fresh alphanumeric variable name
freshVar :: String -> MaybeT Checker String
freshVar s = do
  checkerState <- get
  let v = uniqueVarId checkerState
  let prefix = s ++ "_" ++ ["a", "b", "c", "d"] !! (v `mod` 4)
  let cvar = prefix ++ show v
  put $ checkerState { uniqueVarId = v + 1 }
  return cvar

{- Helpers for error messages and checker control flow -}

unusedVariable :: String -> String
unusedVariable var = "Linear variable `" ++ var ++ "` is never used."

-- | Stops the checker
halt :: MaybeT Checker a
halt = MaybeT (return Nothing)

-- | A helper for raising a type error
illTyped :: Span -> String -> MaybeT Checker a
illTyped = visibleError "Type" halt

-- | A helper for raising a linearity error
illLinearity :: Span -> String -> MaybeT Checker a
illLinearity = visibleError "Linearity" halt

-- | A helper for raising a grading error
illGraded :: Span -> String -> MaybeT Checker ()
illGraded = visibleError "Grading" (return ())

-- | A helper for raising an illtyped pattern (does pretty printing for you)
illTypedPattern :: Span -> Type -> Pattern -> MaybeT Checker a
illTypedPattern s ty pat =
  visibleError "Pattern typing" halt s
    (pretty pat ++ " does not have type " ++ pretty ty)

-- | Errors when a name is used but can't be found
unknownName :: Span -> String -> MaybeT Checker a
unknownName = visibleError "Variable unknown" halt

-- | Helper for constructing error handlers
visibleError :: String -> MaybeT Checker a -> Span -> String -> MaybeT Checker a
visibleError kind next ((0, 0), (0, 0)) s =
  liftIO (hPutStrLn stderr $ kind ++ " error: " ++ s) >> next

visibleError kind next ((sl, sc), (_, _)) s =
  liftIO (hPutStrLn stderr $ show sl ++ ":" ++ show sc ++ ": " ++ kind ++ " error:\n\t"
                   ++ s) >> next

-- | Helper for displaying debugging messages for '-d' mode
dbgMsg :: Bool -> String -> MaybeT Checker ()
dbgMsg dbg = when dbg . liftIO . putStrLn

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
