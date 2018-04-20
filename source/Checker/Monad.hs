-- Defines the 'Checker' monad used in the type checker
-- and various interfaces for working within this monad

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}

module Checker.Monad where

import Data.List (intercalate)
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

import Checker.LaTeX
import Checker.Predicates
import qualified Checker.Primitives as Primitives
import Context
import Syntax.Expr (Id, CKind(..), Span, Type, Kind(..), Coeffect, Pattern,
                    TypeScheme(..), Cardinality, mkId, internalName, Nat)
import Syntax.Pretty
import Utils


-- State of the check/synth functions
newtype Checker a =
  Checker { unwrap :: StateT CheckerState IO a }

evalChecker :: CheckerState -> Checker a -> IO a
evalChecker initialState =
  flip evalStateT initialState . unwrap

runChecker :: CheckerState -> Checker a -> IO (a, CheckerState)
runChecker initialState =
  flip runStateT initialState . unwrap

-- Types or discharged coeffects
data Assumption =
    Linear Type
  | Discharged Type Coeffect
    deriving (Eq, Show)

instance Pretty Assumption where
    pretty (Linear ty) = pretty ty
    pretty (Discharged t c) = ".[" ++ pretty t ++ "]. " ++ pretty c

instance {-# OVERLAPS #-} Pretty (Id, Assumption) where
   pretty (a, b) = pretty a ++ " : " ++ pretty b


data CheckerState = CS
            { -- Fresh variable id
              uniqueVarIdCounter  :: Nat
            -- Local stack of constraints (can be used to build implications)
            , predicateStack :: [Pred]
            -- Type variable context, maps type variables to their kinds
            -- and their quantification
            , tyVarContext   :: Ctxt (Kind, Quantifier)
            -- Context of kind variables and their resolved kind
            -- (used just before solver, to resolve any kind
            -- variables that appear in constraints)
            , kVarContext   :: Ctxt Kind

            -- Guard contexts (all the guards in scope)
            -- which get promoted by branch promotions
            , guardContexts :: [Ctxt Assumption]

            -- Data type information
            , typeConstructors :: Ctxt (Kind, Cardinality) -- the kind of the and number of data constructors
            , dataConstructors :: Ctxt TypeScheme

            -- LaTeX derivation
            , deriv      :: Maybe Derivation
            , derivStack :: [Derivation]
            }
  deriving (Show, Eq) -- for debugging

-- | Initial checker context state
initState :: CheckerState
initState = CS { uniqueVarIdCounter = 0
               , predicateStack = []
               , tyVarContext = emptyCtxt
               , kVarContext = emptyCtxt
               , guardContexts = []
               , typeConstructors = Primitives.typeLevelConstructors
               , dataConstructors = Primitives.dataConstructors
               , deriv = Nothing
               , derivStack = []
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
  checkerState <- get
  (out, localState) <- liftIO $ runChecker checkerState (runMaybeT k)
  let reified = do
        put localState
        MaybeT $ return out
  return (out, reified)

pushGuardContext :: Ctxt Assumption -> MaybeT Checker ()
pushGuardContext ctxt = do
  modify (\state ->
    state { guardContexts = ctxt : guardContexts state })

popGuardContext :: MaybeT Checker (Ctxt Assumption)
popGuardContext = do
  state <- get
  let (c:cs) = guardContexts state
  put (state { guardContexts = cs })
  return c

allGuardContexts :: MaybeT Checker (Ctxt Assumption)
allGuardContexts = do
  state <- get
  return $ concat (guardContexts state)

-- | Helper for creating a few (existential) coeffect variable of a particular
--   coeffect type.
freshCoeffectVar :: Id -> CKind -> MaybeT Checker Id
freshCoeffectVar cvar kind =
    freshCoeffectVarWithBinding cvar kind InstanceQ

-- | Helper for creating a few (existential) coeffect variable of a particular
--   coeffect type.
freshCoeffectVarWithBinding :: Id -> CKind -> Quantifier -> MaybeT Checker Id
freshCoeffectVarWithBinding cvar kind q = do
    freshName <- freshVar (internalName cvar)
    let cvar' = mkId freshName
    registerCoeffectVar cvar' kind q
    return cvar'

-- | Helper for registering a new coeffect variable in the checker
registerCoeffectVar :: Id -> CKind -> Quantifier -> MaybeT Checker ()
registerCoeffectVar v (CConstr constrId) q =
    modify (\st -> st { tyVarContext = (v, (KConstr constrId, q)) : tyVarContext st })
registerCoeffectVar v (CPoly constrId) q =
    modify (\st -> st { tyVarContext = (v, (KVar constrId, q)) : tyVarContext st })

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
      case stack of
         (Conj ps : stack') ->
            put (checkerState { predicateStack = Conj (Impl eVar p p' : ps) : stack' })
         stack' ->
            put (checkerState { predicateStack = Conj [Impl eVar p p'] : stack' })
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

-- | A helper for adding a constraint to the previous frame (i.e.)
-- | if I am in a local context, push it to the global
addConstraintToPreviousFrame :: Constraint -> MaybeT Checker ()
addConstraintToPreviousFrame p = do
        checkerState <- get
        case predicateStack checkerState of
          (ps : Conj ps' : stack) ->
            put (checkerState { predicateStack = ps : Conj (Con p : ps') : stack })
          (ps : stack) ->
            put (checkerState { predicateStack = ps : Conj [Con p] : stack })
          stack ->
            put (checkerState { predicateStack = Conj [Con p] : stack })

-- | Generate a fresh alphanumeric variable name
freshVar :: String -> MaybeT Checker String
freshVar s = do
  checkerState <- get
  let v = uniqueVarIdCounter checkerState
  put checkerState { uniqueVarIdCounter = v + 1 }
  return $ s ++ "." ++ show v

{- Helpers for error messages and checker control flow -}
data TypeError
  = CheckerError (Maybe Span) String
  | GenericError (Maybe Span) String
  | GradingError (Maybe Span) String
  | KindError (Maybe Span) String
  | LinearityError (Maybe Span) String
  | PatternTypingError (Maybe Span) String
  | UnboundVariableError (Maybe Span) String
  | RefutablePatternError (Maybe Span) String

instance UserMsg TypeError where
  title CheckerError {} = "Checker error"
  title GenericError {} = "Type error"
  title GradingError {} = "Grading error"
  title KindError {} = "Kind error"
  title LinearityError {} = "Linearity error"
  title PatternTypingError {} = "Pattern typing error"
  title UnboundVariableError {} = "Unbound variable error"
  title RefutablePatternError {} = "Pattern is refutable"
  location (CheckerError sp _) = sp
  location (GenericError sp _) = sp
  location (GradingError sp _) = sp
  location (KindError sp _) = sp
  location (LinearityError sp _) = sp
  location (PatternTypingError sp _) = sp
  location (UnboundVariableError sp _) = sp
  location (RefutablePatternError sp _) = sp
  msg (CheckerError _ m) = m
  msg (GenericError _ m) = m
  msg (GradingError _ m) = m
  msg (KindError _ m) = m
  msg (LinearityError _ m) = m
  msg (PatternTypingError _ m) = m
  msg (UnboundVariableError _ m) = m
  msg (RefutablePatternError _ m) = m

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

illLinearityMismatch :: (?globals :: Globals) => Span -> [LinearityMismatch] -> MaybeT Checker a
illLinearityMismatch sp mismatches =
  halt $ LinearityError (Just sp) $ intercalate "\n  " $ map mkMsg mismatches
  where
    mkMsg (LinearNotUsed v) =
      "Linear variable `" ++ pretty v ++ "` is never used."
    mkMsg (LinearUsedNonLinearly v) =
      "Variable `" ++ pretty v ++ "` is promoted but its binding is linear; its binding should be under a box."


-- | A helper for raising an illtyped pattern (does pretty printing for you)
illTypedPattern :: (?globals :: Globals) => Span -> Type -> Pattern -> MaybeT Checker a
illTypedPattern sp ty pat =
    halt $ PatternTypingError (Just sp) $
      pretty pat ++ " does not have expected type " ++ pretty ty

-- | A helper for refutable pattern errors
refutablePattern :: (?globals :: Globals) => Span -> Pattern -> MaybeT Checker a
refutablePattern sp p =
  halt $ RefutablePatternError (Just sp) $
        "Pattern match " ++ pretty p ++ " can fail; only \
        \irrefutable patterns allowed in this context"

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
  liftIO = Checker . lift
