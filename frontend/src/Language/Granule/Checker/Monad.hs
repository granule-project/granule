-- Defines the 'Checker' monad used in the type checker
-- and various interfaces for working within this monad

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.Monad where

import Data.List (intercalate)
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

import Language.Granule.Checker.Errors
import Language.Granule.Checker.LaTeX
import Language.Granule.Checker.Predicates
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Context
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Utils

-- State of the check/synth functions
newtype Checker a =
  Checker { unwrap :: StateT CheckerState IO a }

evalChecker :: CheckerState -> Checker a -> IO a
evalChecker initialState =
  flip evalStateT initialState . unwrap

runChecker :: CheckerState -> Checker a -> IO (a, CheckerState)
runChecker initialState =
  flip runStateT initialState . unwrap

-- | Types of discharged coeffects
data Assumption =
    Linear Type
  | Discharged Type Coeffect
    deriving (Eq, Show)

instance Pretty Assumption where
    prettyL l (Linear ty) = prettyL l ty
    prettyL l (Discharged t c) = ".[" <> prettyL l t <> "]. " <> prettyL l c

instance {-# OVERLAPS #-} Pretty (Id, Assumption) where
   prettyL l (a, b) = prettyL l a <> " : " <> prettyL l b


data CheckerState = CS
            { -- Fresh variable id
              uniqueVarIdCounter  :: Nat
            -- Local stack of constraints (can be used to build implications)
            , predicateStack :: [Pred]

            -- Stack of a list of additional knowledge from failed patterns/guards
            -- (i.e. from preceding cases) stored as a list of lists ("frames")
            -- tupling a context of locally bound variables and the predicate
            , guardPredicates :: [[((Ctxt Kind, Pred), Span)]]

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
               , guardPredicates = [[]]
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

-- | Start a new conjunction frame on the predicate stack
newConjunct :: MaybeT Checker ()
newConjunct = do
  checkerState <- get
  put (checkerState { predicateStack = Conj [] : predicateStack checkerState })

-- | Creates a new "frame" on the stack of information about failed cases
-- | This happens when we start a case expression
newCaseFrame :: MaybeT Checker ()
newCaseFrame =
  modify (\st -> st { guardPredicates = [] : guardPredicates st } )

-- | Pop (and don't return) the top of the failed case knowledge stack
-- | This happens when we finish a case expression
popCaseFrame :: MaybeT Checker ()
popCaseFrame =
  modify (\st -> st { guardPredicates = tail (guardPredicates st) })

-- | Takes the top two conjunction frames and turns them into an
-- impliciation
-- The first parameter is a list of any
-- existential variables being introduced in this implication
concludeImplication :: (?globals :: Globals) => Span -> [Id] -> MaybeT Checker ()
concludeImplication s localVars = do
  checkerState <- get
  case predicateStack checkerState of
    (p' : p : stack) -> do

       -- Get all the kinds for the local variables
       localCtxt <- forM localVars $ \v ->
                      case lookup v (tyVarContext checkerState) of
                        Just (k, _) -> return (v, k)
                        Nothing -> error $ "I don't know the kind of "
                                          <> pretty v <> " in "
                                          <> pretty (tyVarContext checkerState)

       case guardPredicates checkerState of

        -- No previous guards in the current frame to provide additional information
        [] : knowledgeStack -> do
          let impl = Impl localVars p p'

          -- Add the implication to the predicate stack
          modify (\st -> st { predicateStack = pushPred impl stack
          -- And add this case to the knowledge stack
                            , guardPredicates = [((localCtxt, p), s)] : knowledgeStack })

        -- Some information currently in the stack frame
        previousGuards : knowledgeStack -> do

           let previousGuardCtxt = concatMap (fst . fst) previousGuards
           let prevGuardPred = Conj (map (snd . fst) previousGuards)

           -- negation of the previous guard
           let guard = foldr (uncurry Exists) (NegPred prevGuardPred) previousGuardCtxt

           -- Implication of p &&& negated previous guards => p'
           let impl = if (isTrivial prevGuardPred)
                        then Impl localVars p p'
                        else Impl localVars (Conj [p, guard]) p'

           let knowledge = ((localCtxt, p), s) : previousGuards

           -- Store `p` (impliciation antecedent) to use in later cases
           -- on the top of the guardPredicates stack
           modify (\st -> st { predicateStack = pushPred impl stack
           -- And add this case to the knowledge stack
                             , guardPredicates = knowledge : knowledgeStack })

    _ -> error "Predicate: not enough conjunctions on the stack"

{-
-- Create a local existential scope
-- NOTE: leaving this here, but this approach is not used and is incompataible
-- with the way that existential variables are generated in the solver
--
existential :: (?globals :: Globals) => Id -> Kind -> MaybeT Checker ()
existential var k = do
  case k of
    -- No need to add variables of kind Type to the predicate
    KType -> return ()
    k -> do
      checkerState <- get
      case predicateStack checkerState of
        (p : stack) -> do
          put (checkerState { predicateStack = Exists var k p : stack })
-}

pushPred :: Pred -> [Pred] -> [Pred]
pushPred p (p' : stack) = appendPred p p' : stack
pushPred p [] = [Conj [p]]

appendPred :: Pred -> Pred -> Pred
appendPred p (Conj ps) = Conj (p : ps)
appendPred p (Exists var k ps) = Exists var k (appendPred p ps)
appendPred _ p = error $ "Cannot append a predicate to " <> show p

-- | A helper for adding a constraint to the context
addConstraint :: Constraint -> MaybeT Checker ()
addConstraint c = do
  checkerState <- get
  case predicateStack checkerState of
    (p : stack) ->
      put (checkerState { predicateStack = appendPred (Con c) p : stack })
    stack ->
      put (checkerState { predicateStack = Conj [Con c] : stack })

-- | A helper for adding a constraint to the previous frame (i.e.)
-- | if I am in a local context, push it to the global
addConstraintToPreviousFrame :: Constraint -> MaybeT Checker ()
addConstraintToPreviousFrame c = do
        checkerState <- get
        case predicateStack checkerState of
          (ps : ps' : stack) ->
            put (checkerState { predicateStack = ps : (appendPred (Con c) ps') : stack })
          (ps : stack) ->
            put (checkerState { predicateStack = ps : Conj [Con c] : stack })
          stack ->
            put (checkerState { predicateStack = Conj [Con c] : stack })

illKindedUnifyVar :: (?globals :: Globals) => Span -> Type -> Kind -> Type -> Kind -> MaybeT Checker a
illKindedUnifyVar sp t1 k1 t2 k2 =
   halt $ KindError (Just sp) $
     "Trying to unify a type `"
     <> pretty t1 <> "` of kind " <> pretty k1
     <> " with a type `"
     <> pretty t2 <> "` of kind " <> pretty k2

illKindedNEq :: (?globals :: Globals) => Span -> Kind -> Kind -> MaybeT Checker a
illKindedNEq sp k1 k2 =
   halt $ KindError (Just sp) $
     "Expected kind `" <> pretty k1 <> "` but got `" <> pretty k2 <> "`"

illLinearityMismatch :: (?globals :: Globals) => Span -> [LinearityMismatch] -> MaybeT Checker a
illLinearityMismatch sp mismatches =
  halt $ LinearityError (Just sp) $ intercalate "\n  " $ map mkMsg mismatches
  where
    mkMsg (LinearNotUsed v) =
      "Linear variable `" <> pretty v <> "` is never used."
    mkMsg (LinearUsedNonLinearly v) =
      "Variable `" <> pretty v <> "` is promoted but its binding is linear; its binding should be under a box."

-- | A helper for raising an illtyped pattern (does pretty printing for you)
illTypedPattern :: (?globals :: Globals) => Span -> Type -> Pattern t -> MaybeT Checker a
illTypedPattern sp ty pat =
    halt $ PatternTypingError (Just sp) $
      pretty pat <> " does not have expected type " <> pretty ty

-- | A helper for refutable pattern errors
refutablePattern :: (?globals :: Globals) => Span -> Pattern t -> MaybeT Checker a
refutablePattern sp p =
  halt $ RefutablePatternError (Just sp) $
        "Pattern match " <> pretty p <> " can fail; only \
        \irrefutable patterns allowed in this context"

-- | Helper for constructing error handlers
halt :: (?globals :: Globals) => TypeError -> MaybeT Checker a
halt err = liftIO (printErr err) >> MaybeT (return Nothing)

typeClashForVariable :: (?globals :: Globals) => Span -> Id -> Type -> Type -> MaybeT Checker a
typeClashForVariable s var t1 t2 =
    halt $ GenericError (Just s)
             $ "Variable " <> pretty var <> " is being used at two conflicting types "
            <> "`" <> pretty t1 <> "` and `" <> pretty t2 <> "`"

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
