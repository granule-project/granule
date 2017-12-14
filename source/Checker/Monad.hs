-- Defines the 'Checker' monad used in the type checker
-- and various interfaces for working within this monad

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}

module Checker.Monad where

import Data.List (intercalate)
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Trans.Reader as MR
import Control.Monad.Reader.Class

import Checker.LaTeX
import Checker.Predicates
import qualified Checker.Primitives as Primitives
import Context
import Syntax.Expr (Id, CKind(..), Span, Type, TypeScheme(..), Kind(..), Coeffect, Pattern)
import Syntax.Pretty
import Utils



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
    deriving (Eq, Show)

instance Pretty Assumption where
    pretty (Linear ty) = pretty ty
    pretty (Discharged t c) = ".[" ++ pretty t ++ "]. " ++ pretty c

instance {-# OVERLAPS #-} Pretty (Id, Assumption) where
   pretty (a, b) = a ++ " : " ++ pretty b


data CheckerState = CS
            { -- Fresh variable id
              uniqueVarId  :: VarCounter
            -- Local stack of constraints (can be used to build implications)
            , predicateStack :: [Pred]
            -- Type variable context, maps type variables to their kinds
            -- and their quantification
            , tyVarContext   :: Ctxt (Kind, Quantifier)
            -- Context of kind variables and their resolved kind
            -- (used just before solver, to resolve any kind
            -- variables that appear in constraints)
            , kVarContext   :: Ctxt Kind
            -- LaTeX derivation
            , deriv      :: Maybe Derivation
            , derivStack :: [Derivation]
            , typeConstructors :: Ctxt Kind
            , dataConstructors :: Ctxt TypeScheme
            }
  deriving (Show, Eq) -- for debugging

-- | Initial checker context state
initState :: CheckerState
initState = CS { uniqueVarId = 0
               , predicateStack = []
               , ckctxt = emptyCtxt
               , cVarCtxt = emptyCtxt
               , deriv = Nothing
               , derivStack = []
               , typeConstructors = Primitives.typeLevelConstructors
               , dataConstructors = Primitives.dataConstructors
               }
  where emptyCtxt = []

-- *** Various helpers for manipulating the context


{- | Useful if a checking procedure is needed which
     may get discarded within a wider checking, e.g., for
     resolving overloaded types via type equality.
     The returned result is stateful but contains no
     updates to the environment: it comprises a pair of
     a pure result (i.e., evaluated and state discarded, and
     a reification of the full state (with updates) should this
     local checking be applied -}
localChecking :: MaybeT Checker b
              -> MaybeT Checker (Maybe b, MaybeT Checker b)
localChecking k = do
  nameMap <- ask
  checkerState <- get
  (out, localState) <- liftIO $ runChecker checkerState nameMap (runMaybeT k)
  let reified = do
        put localState
        MaybeT $ return out
  return (out, reified)

-- | Helper for creating a few (existential) coeffect variable of a particular
--   coeffect type.
freshCoeffectVar :: Id -> CKind -> MaybeT Checker Id
freshCoeffectVar cvar kind =
    freshCoeffectVarWithBinding cvar kind InstanceQ

-- | Helper for creating a few (existential) coeffect variable of a particular
--   coeffect type.
freshCoeffectVarWithBinding :: Id -> CKind -> Quantifier -> MaybeT Checker Id
freshCoeffectVarWithBinding cvar kind q = do
    cvar' <- freshVar cvar
    registerCoeffectVar cvar' kind q
    return cvar'

-- | Helper for registering a new coeffect variable in the checker
registerCoeffectVar :: Id -> CKind -> Quantifier -> MaybeT Checker ()
registerCoeffectVar v (CConstr constrId) q =
  modify (\st -> st { tyVarContext = (v, (KConstr constrId, q)) : tyVarContext st })
registerCoeffectVar v (CPoly constrId) q =
    modify (\st -> st { tyVarContext = (v, (KPoly constrId, q)) : tyVarContext st })

-- | Start a new conjunction frame on the predicate stack
newConjunct :: MaybeT Checker ()
newConjunct = do
  checkerState <- get
  put (checkerState { predicateStack = Conj [] : predicateStack checkerState })

-- | Takes the top two conjunction frames and turns them into an
-- impliciation
-- The first parameter is a list of any
-- existential variables being introduced in this implication
concludeImplication :: [Id] -> MaybeT Checker ()
concludeImplication eVar = do
  checkerState <- get
  case predicateStack checkerState of
    (p' : p : stack) ->
      put (checkerState { predicateStack = Impl eVar p p' : stack })
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
data TypeError
  = CheckerError (Maybe Span) String
  | GenericError (Maybe Span) String
  | GradingError (Maybe Span) String
  | KindError (Maybe Span) String
  | LinearityError (Maybe Span) String
  | PatternTypingError (Maybe Span) String
  | UnboundVariableError (Maybe Span) String

instance UserMsg TypeError where
  title CheckerError {} = "Checker error"
  title GenericError {} = "Type error"
  title GradingError {} = "Grading error"
  title KindError {} = "Kind error"
  title LinearityError {} = "Linearity error"
  title PatternTypingError {} = "Pattern typing error"
  title UnboundVariableError {} = "Unbound variable error"
  location (CheckerError sp _) = sp
  location (GenericError sp _) = sp
  location (GradingError sp _) = sp
  location (KindError sp _) = sp
  location (LinearityError sp _) = sp
  location (PatternTypingError sp _) = sp
  location (UnboundVariableError sp _) = sp
  msg (CheckerError _ m) = m
  msg (GenericError _ m) = m
  msg (GradingError _ m) = m
  msg (KindError _ m) = m
  msg (LinearityError _ m) = m
  msg (PatternTypingError _ m) = m
  msg (UnboundVariableError _ m) = m

illKindedUnifyVar :: (?globals :: Globals) => Span -> Type -> Kind -> Type -> Kind -> MaybeT Checker a
illKindedUnifyVar sp t1 k1 t2 k2 =
    halt $ KindError (Just sp) $
      "Trying to unify a type `"
      ++ pretty t1 ++ "` of kind " ++ pretty k1
      ++ " with a type `"
      ++ pretty t2 ++ "` of kind " ++ pretty k2

illKindedNEq :: (?globals :: Globals) => Span -> Kind -> Kind -> MaybeT Checker a
illKindedNEq sp k1 k2 =
    halt $ KindError (Just sp) $
      "Expected kind `" ++ pretty k1 ++ "` but got `" ++ pretty k2 ++ "`"

data LinearityMismatch =
   LinearNotUsed Id
 | LinearUsedNonLinearly Id
   deriving Show -- for debugging

illLinearityMismatch :: (?globals :: Globals) => Span -> [(Id, Id)] -> [LinearityMismatch] -> MaybeT Checker a
illLinearityMismatch sp nameMap mismatches =
  halt $ LinearityError (Just sp) $ intercalate "\n  " $ map mkMsg mismatches
  where
    mkMsg (LinearNotUsed v) =
      "Linear variable `" ++ unrename nameMap v ++ "` is never used."
    mkMsg (LinearUsedNonLinearly v) =
      "Variable `" ++ unrename nameMap v ++ "` is promoted but its binding is linear; its binding should be under a box."


-- | A helper for raising an illtyped pattern (does pretty printing for you)
illTypedPattern :: (?globals :: Globals) => Span -> Type -> Pattern -> MaybeT Checker a
illTypedPattern sp ty pat =
    halt $ PatternTypingError (Just sp) $
      pretty pat ++ " does not have expected type " ++ pretty ty


-- | Helper for constructing error handlers
halt :: (?globals :: Globals) => TypeError -> MaybeT Checker a
halt err = liftIO (printErr err) >> MaybeT (return Nothing)


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
