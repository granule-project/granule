-- Defines the 'Checker' monad used in the type checker
-- and various interfaces for working within this monad

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.Monad where

import Data.List ((\\), intercalate, nub)
import qualified Data.Map as M
import Data.Maybe (isJust)
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Control.Monad.Identity

import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Errors
import Language.Granule.Checker.Instance (Inst)
import Language.Granule.Checker.LaTeX
import Language.Granule.Checker.Predicates
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Checker.Rewrite.Type (RewriteEnv, buildRewriterEnv)
import Language.Granule.Context

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Helpers (FreshenerState(..), Term, freeVars, freshen)
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

-- Describes where a pattern is fully consuming, i.e. amounts
-- to linear use and therefore triggers other patterns to be counted
-- as linear, e.g.
--    foo 0 = ..
--    foo _ = ..
-- can be typed as foo : Int ->  because the first means
-- consumption is linear
data Consumption = Full | NotFull | Empty deriving (Eq, Show)

-- Given a set of equations, creates an intial vector to describe
-- the consumption behaviour of the patterns (assumes that)
-- the number of patterns is the same for each equation, which
-- is checked elsewhere
initialisePatternConsumptions :: [Equation v a] -> [Consumption]
initialisePatternConsumptions [] = []
initialisePatternConsumptions ((Equation _ _ pats _):_) =
  map (\_ -> NotFull) pats

-- Join information about consumption between branches
joinConsumption :: Consumption -> Consumption -> Consumption
joinConsumption Full _       = Full
joinConsumption Empty Empty  = Empty
joinConsumption _ _          = NotFull

-- Meet information about consumption, across patterns
meetConsumption :: Consumption -> Consumption -> Consumption
meetConsumption NotFull _ = NotFull
meetConsumption _ NotFull = NotFull
meetConsumption Full Full = Full
meetConsumption Empty Empty = Empty
meetConsumption Empty Full = NotFull
meetConsumption Full Empty = NotFull


data IFaceCtxt = IFaceCtxt
  { ifaceParams :: [(Id, Kind)]
  , ifaceSigs :: Ctxt TypeScheme
  , ifaceConstraints :: [Inst]
  } deriving (Show, Eq)

data CheckerState = CS
            { -- Fresh variable id state
              uniqueVarIdCounterMap  :: M.Map String Nat
            , uniqueVarIdCounter     :: Nat
            -- Local stack of constraints (can be used to build implications)
            , predicateStack :: [Pred]

            -- Stack of a list of additional knowledge from failed patterns/guards
            -- (i.e. from preceding cases) stored as a list of lists ("frames")
            -- tupling a context of locally bound variables and the predicate
            , guardPredicates :: [[((Ctxt Kind, Pred), Span)]]

            -- Type variable context, maps type variables to their kinds
            -- and their quantification
            , tyVarContext   :: Ctxt (Kind, Quantifier)

            -- Guard contexts (all the guards in scope)
            -- which get promoted by branch promotions
            , guardContexts :: [Ctxt Assumption]

            -- Records the amount of consumption by patterns in equation equation
            -- used to work out whether an abstract type has been definitly unified with
            -- and can therefore be linear
            , patternConsumption :: [Consumption]

            -- Data type information
            , typeConstructors :: Ctxt (Kind, Cardinality) -- the kind of the and number of data constructors
            , dataConstructors :: Ctxt (TypeScheme, Substitution)

            -- Interface information
            , ifaceContext :: Ctxt IFaceCtxt
            , instanceContext :: Ctxt [(Inst, [Type])]
            , instanceSigs :: M.Map (Inst, Id) TypeScheme
            , expandedConstraints :: Ctxt [Inst]
            -- Context of interface constraints
            , iconsContext :: [Inst]

            -- context of definition types
            , defContext :: Ctxt TypeScheme

            -- LaTeX derivation
            , deriv      :: Maybe Derivation
            , derivStack :: [Derivation]
            }
  deriving (Show, Eq) -- for debugging


-- | Initial checker context state
initState :: CheckerState
initState = CS { uniqueVarIdCounterMap = M.empty
               , uniqueVarIdCounter = 0
               , predicateStack = []
               , guardPredicates = [[]]
               , tyVarContext = emptyCtxt
               , guardContexts = []
               , patternConsumption = []
               , typeConstructors = Primitives.typeConstructors
               , dataConstructors = Primitives.dataConstructors
               , ifaceContext = []
               , instanceContext = []
               , instanceSigs = M.empty
               , expandedConstraints = []
               , iconsContext = []
               , defContext = []
               , deriv = Nothing
               , derivStack = []
               }
  where emptyCtxt = []


-- | Extract useful information for the rewriter from the checker state.
checkerStateToRewriterEnv :: CheckerState -> RewriteEnv
checkerStateToRewriterEnv cs =
    buildRewriterEnv
      (M.toList $ instanceSigs cs)
      (expandedConstraints cs)


-- *** Various helpers for manipulating the context

lookupContext :: (CheckerState -> Ctxt a) -> Id -> MaybeT Checker (Maybe a)
lookupContext ctxtf name = fmap (lookup name . ctxtf) get

getTypeScheme :: Id -> MaybeT Checker (Maybe TypeScheme)
getTypeScheme = lookupContext defContext

-- | @checkDuplicate (ctxtf, descr) sp name@ checks if
-- | @name@ already exists in the context retrieved by
-- | @ctxtf@. If a name already exists, then the program
-- | halts with a `NameClashError`.
checkDuplicate :: (?globals :: Globals) => ((CheckerState -> Ctxt a), String) -> Span -> Id -> MaybeT Checker ()
checkDuplicate (ctxtf, descr) sp name = do
  clash <- isJust . lookup name <$> gets ctxtf
  when clash $ halt $ NameClashError (Just sp) $ concat [descr, " `", pretty name, "` already defined."]

checkDuplicateTyConScope :: (?globals :: Globals) => Span -> Id -> MaybeT Checker ()
checkDuplicateTyConScope sp name = do
  checkDuplicate (typeConstructors, "Type Constructor") sp name
  checkDuplicate (ifaceContext,     "Type Constructor") sp name

registerTyCon :: (?globals :: Globals) => Span -> Id -> Kind -> Cardinality -> MaybeT Checker ()
registerTyCon sp name kind card = do
  checkDuplicateTyConScope sp name
  modify' $ \st -> st { typeConstructors = (name, (kind, card)) : typeConstructors st }


-- | Get the kind of a type constructor.
-- |
-- | This requires that the type constructor is in scope.
getTyConKind :: (?globals :: Globals) => Span -> Id -> MaybeT Checker Kind
getTyConKind sp name = fmap fst $ requireInScope (typeConstructors, "Type constructor") sp name


registerInterface :: (?globals :: Globals) => Span -> Id -> [(Id, Kind)] -> [Inst] -> Ctxt TypeScheme -> MaybeT Checker ()
registerInterface sp name params constrs sigs = do
  let ifaceCtxt = IFaceCtxt { ifaceParams = params
                            , ifaceSigs = sigs
                            , ifaceConstraints = constrs
                            }
  checkDuplicateTyConScope sp name
  modify' $ \st -> st { ifaceContext = (name, ifaceCtxt) : ifaceContext st }


registerExpandedConstraints :: Span -> Id -> [Inst] -> MaybeT Checker ()
registerExpandedConstraints sp name constrs =
    modify' $ \st -> st { expandedConstraints = (name, constrs) : expandedConstraints st }


getConstraintsExpanded :: (?globals :: Globals) => Span -> Id -> MaybeT Checker [Inst]
getConstraintsExpanded sp n = do
    maybeConstrs <- lookupContext expandedConstraints n
    maybe (halt . GenericError (Just sp) $
                    "internal error: attempted to look up expanded constraints for '"
                    <> pretty n <> "' before it has been registered") pure maybeConstrs


-- | Get the set of interface constraints in scope.
getIConstraints :: (?globals :: Globals) => MaybeT Checker [Inst]
getIConstraints = fmap iconsContext get


putIcons :: [Inst] -> MaybeT Checker ()
putIcons ts = modify' $ \st -> st { iconsContext = nub ts }


addIConstraint :: Inst -> MaybeT Checker ()
addIConstraint ty =
  modify' $ \st -> st { iconsContext = nub $ ty : iconsContext st }


-------------------------------
----- Sub-checker helpers -----
-------------------------------


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


-- | @withFreeVarsBound ty q c@ executes the checker @c@, but with
-- | free variables in @ty@ bound with quantifier @q@.
withFreeVarsBound :: (?globals :: Globals, Term t) => t -> Quantifier -> MaybeT Checker a -> MaybeT Checker a
withFreeVarsBound ty q c = do
  names <- fmap (fmap fst . tyVarContext) get
  -- make sure we don't re-bind any already-bound variables
  let newVars = freeVars ty \\ names
      binds = fmap (\v -> (v, KType)) newVars
  withBindings binds q c


-- | Run the checker with the given bindings present.
withBindings :: [(Id, Kind)] -> Quantifier -> MaybeT Checker a -> MaybeT Checker a
withBindings binds q c = do
  tyVarContextInit <- fmap tyVarContext get
  modify $ \st -> st { tyVarContext = fmap (\(v,k) -> (v, (k, q))) binds <> tyVarContext st }
  c <* modify (\st -> st { tyVarContext = tyVarContextInit })


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
allGuardContexts = concat . guardContexts <$> get

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
-- implication
-- The first parameter is a list of any
-- existential variables being introduced in this implication
concludeImplication :: (?globals :: Globals) => Span -> Ctxt Kind -> MaybeT Checker ()
concludeImplication s localCtxt = do
  checkerState <- get
  case predicateStack checkerState of
    (p' : p : stack) -> do

       case guardPredicates checkerState of

        [] -> error "Internal bug: Guard predicate is [] and should not be"

        -- No previous guards in the current frame to provide additional information
        [] : knowledgeStack -> do
          let impl = Impl localCtxt p p'

          -- Add the implication to the predicate stack
          modify (\st -> st { predicateStack = pushPred impl stack
          -- And add this case to the knowledge stack
                            , guardPredicates = [((localCtxt, p), s)] : knowledgeStack })

        -- Some information currently in the stack frame
        previousGuards : knowledgeStack -> do

           let previousGuardCtxt = concatMap (fst . fst) previousGuards
           let prevGuardPred = Conj (map (snd . fst) previousGuards)

           freshenedPrevGuardPred <- freshenPred $ Impl previousGuardCtxt (Conj []) (NegPred prevGuardPred)
           let (Impl freshPrevGuardCxt _ freshPrevGuardPred) = freshenedPrevGuardPred

           -- Implication of p .&& negated previous guards => p'
           let impl@(Impl implCtxt implAntecedent _) =
                -- TODO: turned off this feature for now by putting True in the guard here
                if True -- isTrivial freshPrevGuardPred
                  then (Impl localCtxt p p')
                  else (Impl (localCtxt <> freshPrevGuardCxt)
                                 (Conj [p, freshPrevGuardPred]) p')

           let knowledge = ((implCtxt, implAntecedent), s) : previousGuards

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

addPredicate :: Pred -> MaybeT Checker ()
addPredicate p = do
  checkerState <- get
  case predicateStack checkerState of
    (p' : stack) ->
      put (checkerState { predicateStack = appendPred p p' : stack })
    stack ->
      put (checkerState { predicateStack = Conj [p] : stack })

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

-- | Retrieve the value associated with a name in the retrieved
-- | context, failing if it doesn't
requireInScope :: (?globals :: Globals) => (CheckerState -> Ctxt a, String) -> Span -> Id -> MaybeT Checker a
requireInScope (ctxtf, descr) sp name = do
  def <- lookup name <$> gets ctxtf
  case def of
    Nothing -> notInScope descr sp name
    Just d -> pure d

notInScope :: (?globals :: Globals) => String -> Span -> Id -> MaybeT Checker a
notInScope desc sp name = halt $
  UnboundVariableError (Just sp) $ concat [desc, " `", pretty name, "` is not in scope."]

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
    mkMsg NonLinearPattern =
      "Wildcard pattern `_` allowing a value to be discarded in a position which requires linear use."

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

typeClash :: (?globals :: Globals) => Span -> Type -> Type -> MaybeT Checker a
typeClash s t1 t2 =
  halt $ GenericError (Just s) $
    if pretty t1 == pretty t2
      then "Expected `" <> pretty t1 <> "` but got `" <> pretty t2 <> "` coming from a different binding"
      else "Expected `" <> pretty t1 <> "` but got `" <> pretty t2 <> "`"

-- | Helper for constructing error handlers
halt :: (?globals :: Globals) => CheckerError -> MaybeT Checker a
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

freshenPred :: Pred -> MaybeT Checker Pred
freshenPred pred = do
    st <- get
    -- Run the freshener using the checkers unique variable id
    let (pred', freshenerState) =
         runIdentity $ runStateT (freshen pred)
          (FreshenerState { counter = 1 + uniqueVarIdCounter st, varMap = [], tyMap = []})
    -- Update the unique counter in the checker
    put (st { uniqueVarIdCounter = counter freshenerState })
    return pred'
