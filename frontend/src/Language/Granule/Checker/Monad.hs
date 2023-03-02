
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ImplicitParams #-}

{-# options_ghc -fno-warn-incomplete-uni-patterns #-}

-- | Defines the 'Checker' monad used in the type checker
-- | and various interfaces for working within this monad
module Language.Granule.Checker.Monad where

import Data.Maybe (mapMaybe)
import Data.Either (partitionEithers)
import Data.Foldable (toList)
import Data.Functor ( ($>) )
import Data.List (intercalate, transpose)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as M
import Data.Semigroup (sconcat)
import Control.Monad.State.Strict
import Control.Monad.Except
import Control.Monad.Identity
import System.FilePath (takeBaseName)

import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.LaTeX
import Language.Granule.Checker.Predicates
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Context

import Language.Granule.Syntax.Program
import Language.Granule.Syntax.Expr (Operator, Expr)
import Language.Granule.Syntax.Helpers (FreshenerState(..), freshen, Term(..))
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Utils

-- State of the check/synth functions
newtype Checker a = Checker
  { unChecker :: ExceptT (NonEmpty CheckerError) (StateT CheckerState IO) a }
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadState CheckerState
    , MonadError (NonEmpty CheckerError)
    , MonadIO
    , MonadFail
    )

type CheckerResult r = Either (NonEmpty CheckerError) r

evalChecker :: CheckerState -> Checker a -> IO (CheckerResult a)
evalChecker initialState (Checker k) = evalStateT (runExceptT k) initialState

runChecker :: CheckerState -> Checker a -> IO (CheckerResult a, CheckerState)
runChecker initialState (Checker k) = runStateT (runExceptT k) initialState

-- | Repeat a checker action for every input value and only fail at the end if
-- any action failed.
runAll :: (a -> Checker b) -> [a] -> Checker [b]
runAll f xs = do
  st <- get
  (results, st) <- liftIO $ runAllCheckers st (map f xs)
  case partitionEithers results of
    ([], successes) -> put st $> successes
    -- everything succeeded, so `put` the state and carry on
    (err:errs, _) -> throwError $ sconcat (err:|errs)
    -- combine all errors and fail
  where
    runAllCheckers st [] = pure ([], st)
    runAllCheckers st (c:cs) = do
      (r, st) <- runChecker st c
      (rs,st) <- runAllCheckers st cs
      pure (r:rs, st)

-- | Types of discharged coeffects
data Assumption
  = Linear     Type
  | Discharged Type Coeffect
  | Ghost      Coeffect
    deriving (Eq, Show)

ghostType :: Type
ghostType = tyCon ".ghost"

getAssumptionType :: Assumption -> Type
getAssumptionType (Linear t) = t
getAssumptionType (Discharged t _) = t
getAssumptionType (Ghost c) = ghostType

instance Term Assumption where
  freeVars (Linear t) = freeVars t
  freeVars (Discharged t c) = freeVars t ++ freeVars c
  freeVars (Ghost c) = freeVars c

instance Pretty Assumption where
    pretty (Linear ty) = pretty ty
    pretty (Discharged t c) = ".[" <> pretty t <> "]. " <> prettyNested c
    pretty (Ghost c) = "ghost(" <> pretty c <> ")"

instance {-# OVERLAPS #-} Pretty (Id, Assumption) where
   pretty (a, b) = pretty a <> " : " <> pretty b

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
initialisePatternConsumptions ((Equation _ _ _ _ pats _):_) =
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

data CheckerState = CS
            { -- Fresh variable id state
              uniqueVarIdCounterMap  :: M.Map String Int
            , uniqueVarIdCounter     :: Int
            -- Local stack of constraints (can be used to build implications)
            , predicateStack :: [Pred]

            -- Stack of a list of additional knowledge from failed patterns/guards
            -- (i.e. from preceding cases) stored as a list of lists ("frames")
            -- tupling a context of locally bound variables and the predicate
            , guardPredicates :: [[((Ctxt Kind, Pred), Span)]]

            -- Type variable context, maps type variables to their kinds
            -- and their quantification
            , tyVarContext   :: Ctxt (Type, Quantifier)

            -- Guard contexts (all the guards in scope)
            -- which get promoted  by branch promotions
            , guardContexts :: [Ctxt Assumption]

            -- Records the amount of consumption by patterns in equation equation
            -- used to work out whether an abstract type has been definitly unified with
            -- and can therefore be linear
            , patternConsumption :: [Consumption]

            -- Data type information
            --  map of type constructor names to their the kind,
            --  data constructors, and whether indexed (True = Indexed, False = Not-indexed)
            , typeConstructors :: Ctxt (Type, [Id], Bool)
            -- map of data constructors and their types and substitutions
            , dataConstructors :: Ctxt (TypeScheme, Substitution)

            -- LaTeX derivation
            , deriv      :: Maybe Derivation
            , derivStack :: [Derivation]

            -- Names from modules which are hidden
            , allHiddenNames :: M.Map Id ModuleName

            -- The type of the current equation.
            , equationTy :: Maybe Type
            , equationName :: Maybe Id

            -- Definitions that have been triggered during type checking
            -- by the auto deriver (so we know we need them in the interpreter)
            , derivedDefinitions :: [((Id, Type), (TypeScheme, Def () ()))]
            -- Warning accumulator
            -- , warnings :: [Warning]

            , wantedTypeConstraints :: [Type]

            -- flag to find out if constraints got added
            , addedConstraints :: Bool
            }
  deriving (Eq, Show) -- for debugging

-- | Initial checker context state
initState :: (?globals :: Globals) => CheckerState
initState = CS { uniqueVarIdCounterMap = M.empty
               , uniqueVarIdCounter = 0
               , predicateStack = []
               , guardPredicates = [[]]
               , tyVarContext = []
               , guardContexts = []
               , patternConsumption = []
               , typeConstructors = Primitives.typeConstructors
               , dataConstructors = []
               , deriv = Nothing
               , derivStack = []
               , allHiddenNames = M.empty
               , equationTy = Nothing
               , equationName = Nothing
               , derivedDefinitions = []
               , wantedTypeConstraints = []
               , addedConstraints = False
               }

-- *** Various helpers for manipulating the context

-- Look up a data constructor, taking into account the possibility that it
-- may be hidden to the current module
lookupDataConstructor :: Span -> Id -> Checker (Maybe (TypeScheme, Substitution))
lookupDataConstructor sp constrName = do
  st <- get
  case M.lookup constrName (allHiddenNames st) of
    Nothing -> return $ lookup constrName (dataConstructors st)
    Just mod ->
      -- If the constructor is hidden but we are inside that module...
      if mod == takeBaseName (filename sp)
        -- .. then its fine
        then return $ lookup constrName (dataConstructors st)
        -- Otheriwe this is truly hidden
        else return Nothing

lookupPatternMatches :: Span -> Id -> Checker (Maybe [Id])
lookupPatternMatches sp constrName = do
  st <- get
  return $ snd3 <$> lookup constrName (typeConstructors st)

-- Return the data constructors of all types in the environment
allDataConstructorNames :: Checker (Ctxt [Id])
allDataConstructorNames = do
  st <- get
  return $ ctxtMap (\(_, datas, _) -> datas) (typeConstructors st)

allDataConstructorNamesForType :: Type -> Checker [Id]
allDataConstructorNamesForType ty = do
    st <- get
    return $ mapMaybe go (typeConstructors st)
  where
    go :: (Id, (Type, a, Bool)) -> Maybe Id
    go (con, (k, _, _)) = if k == ty then Just con else Nothing

{- | Given a computation in the checker monad, peek the result without
actually affecting the current checker environment. Unless the value is
discarded, the rhs result computation must be run! This is useful for
example when resolving overloaded operators, where we don't want to report
unification errors that arise during operator resultion to the user.
-}
peekChecker :: Checker a -> Checker (CheckerResult a, Checker ())
peekChecker k = do
  checkerState <- get
  (result, localState) <- liftIO $ runChecker checkerState k
  pure (result, put localState)

attemptChecker :: Checker a -> Checker (Bool, Checker ())
attemptChecker k = do
  checkerState <- get
  (result, localState) <- liftIO $ runChecker checkerState k
  case result of
    Right _ -> return (True, put localState)
    Left  _ -> return (False, put localState)

(<|>) :: Checker a -> Checker a -> Checker a
m1 <|> m2 = do
  (result, putCheckerComputation) <- peekChecker m1
  case result of
    -- Failed
    Left _ -> m2
    Right res -> do
      putCheckerComputation
      return res

pushGuardContext :: Ctxt Assumption -> Checker ()
pushGuardContext ctxt = do
  modify (\state ->
    state { guardContexts = ctxt : guardContexts state })

popGuardContext :: Checker (Ctxt Assumption)
popGuardContext = do
  state <- get
  let (c, cs) = case guardContexts state of
                  (c:cs) -> (c,cs)
                  [] -> error "Internal error. Empty guard context."
  put (state { guardContexts = cs })
  return c

allGuardContexts :: Checker (Ctxt Assumption)
allGuardContexts = concat . guardContexts <$> get

-- | Start a new conjunction frame on the predicate stack
newConjunct :: Checker ()
newConjunct = do
  checkerState <- get
  put (checkerState { predicateStack = Conj [] : predicateStack checkerState })

-- | Creates a new "frame" on the stack of information about failed cases
-- | This happens when we start a case expression
newCaseFrame :: Checker ()
newCaseFrame =
  modify (\st -> st { guardPredicates = [] : guardPredicates st } )

-- | Pop (and don't return) the top of the failed case knowledge stack
-- | This happens when we finish a case expression
popCaseFrame :: Checker ()
popCaseFrame =
  modify (\st -> st { guardPredicates = tail (guardPredicates st) })

-- | Takes the top two conjunction frames and turns them into an
-- implication
-- The first parameter is a list of any
-- existential variables being introduced in this implication
concludeImplication :: Span -> Ctxt Kind -> Checker ()
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

           -- Build the guard theorem to also include all of the 'context' of things
           -- which also need to hold (held in `stack`)
           let guardTheorem = Conj (implAntecedent : stack)
           let knowledge = ((implCtxt, guardTheorem), s) : previousGuards

           -- Store `p` (impliciation antecedent) to use in later cases
           -- on the top of the guardPredicates stack
           modify (\st -> st { predicateStack = pushPred impl stack
           -- And add this case to the knowledge stack
                             , guardPredicates = knowledge : knowledgeStack })


    _ -> error "Predicate: not enough conjunctions on the stack"

-- Create an existential scope at the top level (i.e., not locally scopped)
existentialTopLevel :: Id -> Kind -> Checker ()
existentialTopLevel var k = do
  st <- get
  put $ st { tyVarContext = (var, (k, InstanceQ)) : tyVarContext st }

-- Create a local existential scope
existential :: Id -> Kind -> Checker ()
existential var k = do
  case k of
    -- No need to add variables of kind Type to the predicate
    Type _ -> return ()
    k -> do
      checkerState <- get
      case predicateStack checkerState of
        (p : stack) -> do
          put (checkerState { predicateStack = Exists var k p : stack })
        [] ->
          put (checkerState { predicateStack = [Exists var k (Conj [])] })

pushPred :: Pred -> [Pred] -> [Pred]
pushPred p (p' : stack) = appendPred p p' : stack
pushPred p [] = [Conj [p]]

appendPred :: Pred -> Pred -> Pred
appendPred p (Conj ps) = Conj (p : ps)
appendPred p (Exists var k ps) = Exists var k (appendPred p ps)
appendPred _ p = error $ "Cannot append a predicate to " <> show p

addPredicate :: Pred -> Checker ()
addPredicate p = do

  checkerState <- get
  case predicateStack checkerState of
    (p' : stack) ->
      put (checkerState { predicateStack = appendPred p p' : stack })
    stack ->
      put (checkerState { predicateStack = Conj [p] : stack })

-- | A helper for adding a constraint to the context
addConstraint :: Constraint -> Checker ()
addConstraint c = do
  checkerState <- get
  case predicateStack checkerState of
    (p : stack) ->
      put (checkerState { predicateStack = appendPred (Con c) p : stack, addedConstraints = True })
    stack ->
      put (checkerState { predicateStack = Conj [Con c] : stack, addedConstraints = True })

resetAddedConstraintsFlag :: Checker ()
resetAddedConstraintsFlag = modify (\st -> st { addedConstraints = False })

-- | A helper for adding a constraint to the previous frame (i.e.)
-- | if I am in a local context, push it to the global
addConstraintToPreviousFrame :: Constraint -> Checker ()
addConstraintToPreviousFrame c = do
        checkerState <- get
        case predicateStack checkerState of
          (ps : ps' : stack) ->
            put (checkerState { predicateStack = ps : (appendPred (Con c) ps') : stack, addedConstraints = True })
          (ps : stack) ->
            put (checkerState { predicateStack = ps : Conj [Con c] : stack, addedConstraints = True })
          stack ->
            put (checkerState { predicateStack = Conj [Con c] : stack, addedConstraints = True })

-- Given a coeffect type variable and a coeffect kind,
-- replace any occurence of that variable in a context
updateCoeffectType :: Id -> Type -> Checker ()
updateCoeffectType tyVar k = do
   modify (\checkerState ->
    checkerState
     { tyVarContext = rewriteCtxt (tyVarContext checkerState) })
 where
   rewriteCtxt :: Ctxt (Type, Quantifier) -> Ctxt (Type, Quantifier)
   rewriteCtxt [] = []
   rewriteCtxt ((name, ((TyVar kindVar), q)) : ctxt)
    | tyVar == kindVar = (name, (k, q)) : rewriteCtxt ctxt
   rewriteCtxt (x : ctxt) = x : rewriteCtxt ctxt

-- | Convenience function for throwing a single error
throw :: CheckerError -> Checker a
throw = throwError . pure

illLinearityMismatch :: Span -> NonEmpty LinearityMismatch -> Checker a
illLinearityMismatch sp ms = throwError $ fmap (LinearityError sp) ms

registerWantedTypeConstraints :: [Type] -> Checker ()
registerWantedTypeConstraints ts =
  modify (\st -> st { wantedTypeConstraints = ts ++ wantedTypeConstraints st })

{- Helpers for error messages and checker control flow -}
data CheckerError
  = HoleMessage
    { errLoc      :: Span,
      holeTy      :: Type,
      context     :: Ctxt Assumption,
      tyContext   :: Ctxt (Type, Quantifier),
      -- Tracks whether a variable is split
      holeVars :: Ctxt Bool,
      -- Used for synthesising programs
      cases       :: [([Pattern ()], Expr () Type)] }
  | TypeError
    { errLoc :: Span, tyExpected :: Type, tyActual :: Type }
  | TypeErrorAtLevel
    { errLoc :: Span, tyExpectedL :: Type , tyActualL :: Type }
  | GradingError
    { errLoc :: Span, errConstraint :: Neg Constraint }
  | KindMismatch
    { errLoc :: Span, tyActualK :: Maybe Type, kExpected :: Kind, kActual :: Kind }
  | SortMismatch
    { errLoc :: Span, kActualS :: Maybe Type, sExpected :: Type, sActual :: Type }
  | KindError
    { errLoc :: Span, errTy :: Type, errKL :: Type }
  | KindCannotFormSet
    { errLoc :: Span, errK :: Kind }
  | KindsNotEqual
    { errLoc :: Span, errK1 :: Kind, errK2 :: Kind }
  | IntervalGradeKindError
    { errLoc :: Span, errTy1 :: Type, errTy2 :: Type }
  | LinearityError
    { errLoc :: Span, linearityMismatch :: LinearityMismatch }
  | UniquenessError
    { errLoc :: Span, uniquenessMismatch :: UniquenessMismatch }
  | UnpromotableError
    { errLoc :: Span, errTy :: Type }
  | PatternTypingError
    { errLoc :: Span, errPat :: Pattern (), tyExpected :: Type }
  | PatternTypingMismatch
    { errLoc :: Span, errPat :: Pattern (), tyExpected :: Type, tyActual :: Type }
  | PatternArityError
    { errLoc :: Span, errId :: Id }
  | UnboundVariableError
    { errLoc :: Span, errId :: Id }
  | UnboundTypeVariable
    { errLoc :: Span, errId :: Id }
  | RefutablePatternError
    { errLoc :: Span, errPat :: Pattern () }
  | TypeConstructorNameClash -- TODO: duplicate?
    { errLoc :: Span, errId :: Id }
  | DuplicateBindingError
    { errLoc :: Span, duplicateBinding :: String }
  | UnificationError
    { errLoc :: Span, errTy1 :: Type, errTy2 :: Type }
  | UnificationKindError
    { errLoc :: Span, errTy1 :: Type, errK1 :: Kind, errTy2 :: Type, errK2 :: Kind }
  | TypeVariableMismatch
    { errLoc :: Span, errVar :: Id, errTy1 :: Type, errTy2 :: Type }
  | UndefinedEqualityError
    { errLoc :: Span, errTy1 :: Type, errTy2 :: Type, errKL :: Type }
  | CoeffectUnificationError
    { errLoc :: Span, errTy1 :: Type, errTy2 :: Type, errC1 :: Coeffect, errC2 :: Coeffect }
  | DataConstructorTypeVariableNameClash
    { errLoc :: Span, errDataConstructorId :: Id, errTypeConstructor :: Id, errVar :: Id }
  | DataConstructorNameClashError
    { errLoc :: Span, errId :: Id }
  | EffectMismatch
    { errLoc :: Span, effExpected :: Type, effActual :: Type }
  | UnificationDisallowed
    { errLoc :: Span, errTy1 :: Type, errTy2 :: Type }
  | UnificationFail
    { errLoc :: Span, errVar :: Id, errTy :: Type, errKind :: Kind, tyIsConcrete :: Bool  }
  | UnificationFailGeneric
    { errLoc :: Span, errSubst1 :: Substitutors, errSubst2 :: Substitutors }
  | OccursCheckFail
    { errLoc :: Span, errVar :: Id, errTy :: Type }
  | SessionDualityError
    { errLoc :: Span, errTy1 :: Type, errTy2 :: Type }
  | NoUpperBoundError
    { errLoc :: Span, errTy1 :: Type, errTy2 :: Type }
  | DisallowedCoeffectNesting
    { errLoc :: Span, errTyOuter :: Type, errTyInner :: Type }
  | UnboundDataConstructor
    { errLoc :: Span, errId :: Id }
  | UnboundTypeConstructor
    { errLoc :: Span, errId :: Id }
  | TooManyPatternsError
    { errLoc :: Span, errPats :: NonEmpty (Pattern ()), tyExpected :: Type, tyActual :: Type }
  | DataConstructorReturnTypeError
    { errLoc :: Span, idExpected :: Id, idActual :: Id }
  | MalformedDataConstructorType
    { errLoc :: Span, errTy :: Type }
  | ExpectedEffectType
    { errLoc :: Span, errTy :: Type }
  | ExpectedOptionalEffectType
    { errLoc :: Span, errTy :: Type }
  | LhsOfApplicationNotAFunction
    { errLoc :: Span, errTy :: Type }
  | FailedOperatorResolution
    { errLoc :: Span, errOp :: Operator, errTy :: Type }
  | NeedTypeSignature
    { errLoc :: Span, errExpr :: Expr () () }
  | SolverErrorCounterExample
    { errLoc :: Span, errDefId :: Id, errPred :: Pred, message :: String }
  | SolverErrorFalsifiableTheorem
    { errLoc :: Span, errDefId :: Id, errPred :: Pred }
  | SolverError
    { errLoc :: Span, errMsg :: String, errPred :: Pred }
  | SolverTimeout
    { errLoc :: Span, errSolverTimeoutMillis :: Integer, errDefId :: Id, errContext :: String, errPred :: Pred }
  | UnifyGradedLinear
    { errLoc :: Span, errLinearOrGraded :: Id }
  | ImpossiblePatternMatch
    { errLoc :: Span, errId :: Id, errPred :: Pred }
  | ImpossiblePatternMatchTrivial
    { errLoc :: Span, errId :: Id, errUnsats :: [Constraint] }
  | NameClashTypeConstructors -- we arbitrarily use the second thing that clashed as the error location
    { errLoc :: Span, errDataDecl :: DataDecl, otherDataDecls :: NonEmpty DataDecl }
  | NameClashDataConstructors -- we arbitrarily use the second thing that clashed as the error location
    { errLoc :: Span, errDataConstructor :: DataConstr, otherDataConstructors :: NonEmpty DataConstr }
  | NameClashDefs -- we arbitrarily use the second thing that clashed as the error location
    { errLoc :: Span, errDef :: Def () (), otherDefs :: NonEmpty (Def () ()) }
  | UnexpectedTypeConstructor
    { errLoc :: Span, tyConExpected :: Id, tyConActual :: Id }
  | InvalidTypeDefinition
    { errLoc :: Span, errTy :: Type }
  | InvalidHolePosition
    { errLoc :: Span }
  | UnknownResourceAlgebra
    { errLoc :: Span, errTy :: Type, errK :: Kind }
  | CaseOnIndexedType
    { errLoc :: Span, errTy :: Type }
  | OperatorUndefinedForKind
    { errLoc :: Span, errK :: Kind, errTyOp :: TypeOperator }
  | WrongLevel
    { errLoc :: Span, errTy :: Type, level :: Int }
  | ImpossibleKindSynthesis
    { errLoc :: Span, errTy :: Type }
  | NaturalNumberAtWrongKind
    { errLoc :: Span, errTy :: Type, errK :: Kind }
  | InvalidPromotionError
    { errLoc :: Span, errTy :: Type }
  | TypeConstraintNotSatisfied
    { errLoc :: Span, errTy :: Type }
  deriving (Show)

instance UserMsg CheckerError where
  location = errLoc

  title HoleMessage{} = "Found a goal"
  title TypeError{} = "Type error"
  title TypeErrorAtLevel{} = "Type error"
  title GradingError{} = "Grading error"
  title KindMismatch{} = "Kind mismatch"
  title SortMismatch{} = "Sort mismatch"
  title KindError{} = "Kind error"
  title KindCannotFormSet{} = "Kind error"
  title KindsNotEqual{} = "Kind error"
  title IntervalGradeKindError{} = "Interval kind error"
  title LinearityError{} = "Linearity error"
  title UniquenessError{} = "Uniqueness error"
  title UnpromotableError{} = "Unpromotable error"
  title PatternTypingError{} = "Pattern typing error"
  title PatternTypingMismatch{} = "Pattern typing mismatch"
  title PatternArityError{} = "Pattern arity error"
  title UnboundVariableError{} = "Unbound variable error"
  title UnboundTypeVariable{} = "Unbound type variable"
  title RefutablePatternError{} = "Pattern is refutable"
  title TypeConstructorNameClash{} = "Type constructor name clash"
  title DataConstructorTypeVariableNameClash{} = "Type variable name clash"
  title DuplicateBindingError{} = "Duplicate binding"
  title UnificationError{} = "Unification error"
  title UnificationKindError{} = "Unification kind error"
  title TypeVariableMismatch{} = "Type variable mismatch"
  title UndefinedEqualityError{} = "Undefined kind equality"
  title CoeffectUnificationError{} = "Coeffect unification error"
  title DataConstructorNameClashError{} = "Data constructor name clash"
  title EffectMismatch{} = "Effect mismatch"
  title UnificationDisallowed{} = "Unification disallowed"
  title UnificationFail{} = "Unification failed"
  title UnificationFailGeneric{} = "Unification failed"
  title OccursCheckFail{} = "Unification failed"
  title SessionDualityError{} = "Session duality error"
  title NoUpperBoundError{} = "Type upper bound"
  title DisallowedCoeffectNesting{} = "Bad coeffect nesting"
  title UnboundDataConstructor{} = "Unbound data constructor"
  title UnboundTypeConstructor{} = "Unbound type constructor"
  title TooManyPatternsError{} = "Too many patterns"
  title DataConstructorReturnTypeError{} = "Wrong return type in data constructor"
  title MalformedDataConstructorType{} = "Malformed data constructor type"
  title ExpectedEffectType{} = "Type error"
  title ExpectedOptionalEffectType{} = "Type error"
  title LhsOfApplicationNotAFunction{} = "Type error"
  title FailedOperatorResolution{} = "Operator resolution failed"
  title NeedTypeSignature{} = "Type signature needed"
  title SolverErrorCounterExample{} = "Counter example"
  title SolverErrorFalsifiableTheorem{} = "Falsifiable theorem"
  title SolverError{} = "Solver error"
  title SolverTimeout{} = "Solver timeout"
  title UnifyGradedLinear{} = "Type error"
  title ImpossiblePatternMatch{} = "Impossible pattern match"
  title ImpossiblePatternMatchTrivial{} = "Impossible pattern match"
  title NameClashTypeConstructors{} = "Type constructor name clash"
  title NameClashDataConstructors{} = "Data constructor name clash"
  title NameClashDefs{} = "Definition name clash"
  title UnexpectedTypeConstructor{} = "Wrong return type in value constructor"
  title InvalidTypeDefinition{} = "Invalid type definition"
  title InvalidHolePosition{} = "Invalid hole position"
  title UnknownResourceAlgebra{} = "Type error"
  title CaseOnIndexedType{} = "Type error"
  title OperatorUndefinedForKind{} = "Kind error"
  title WrongLevel{} = "Type error"
  title ImpossibleKindSynthesis{} = "Kind error"
  title NaturalNumberAtWrongKind{} = "Kind error"
  title InvalidPromotionError{} = "Type error"
  title TypeConstraintNotSatisfied{} = "Type constraint error"

  msg HoleMessage{..} =
    "\n   Expected type is: `" <> pretty holeTy <> "`"
    <>
    -- Print the context if there is anything to use
    (if null context
      then ""
      else "\n\n   Context:" <> concatMap (\x -> "\n     " ++ pretty x) context)
    <>
    (if null tyContext
      then ""
      else "\n\n   Type context:" <> concatMap (\(v, (t , _)) ->  "\n     "
                                                <> pretty v
                                                <> " : " <> pretty t) tyContext)
    <>
    (if null relevantVars
      then ""
      else if null cases
        then "\n\n   No case splits could be found for: " <> intercalate ", " (map pretty relevantVars)
        else "\n\n   Case splits for " <> intercalate ", " (map pretty relevantVars) <> ":\n     " <>
             intercalate "\n     " (formatCases relevantCases))

    where
      -- Extract those cases which correspond to a split variable in holeVars.
      relevantCases :: [[Pattern ()]]
      relevantCases = map (map snd . filter fst . zip (map snd holeVars) . fst) cases

      relevantVars :: [Id]
      relevantVars = map fst (filter snd holeVars)

      formatCases :: [[Pattern ()]] -> [String]
      formatCases = map unwords . transpose . map padToLongest . transpose . map (map prettyNested)

      -- Pad all strings in a list so they match the length of the longest.
      padToLongest :: [String] -> [String]
      padToLongest xs =
        let size = maximum (map length xs)
        in  map (\s -> s ++ replicate (size - length s) ' ') xs


  msg TypeError{..} = if pretty tyExpected == pretty tyActual
    then "Expected `" <> pretty tyExpected <> "` but got `" <> pretty tyActual <> "` coming from a different binding"
    else "Expected `" <> pretty tyExpected <> "` but got `" <> pretty tyActual <> "`"

  msg TypeErrorAtLevel{..} = if pretty tyExpectedL == pretty tyActualL
    then "Expected `" <> pretty tyExpectedL <> "` but got `" <> pretty tyActualL <> "` coming from a different binding"
    else "Expected `" <> pretty tyExpectedL <> "` but got `" <> pretty tyActualL <> "`"


  msg GradingError{ errConstraint } = pretty errConstraint

  msg KindMismatch{..}
    = case tyActualK of
        Nothing -> "Expected kind `" <> pretty kExpected <> "` but got `" <> pretty kActual <> "`"
        Just ty -> "Expected kind `" <> pretty kExpected <> "` for type `" <> pretty ty <> "` but actual kind is `" <> pretty kActual <> "`"

  msg SortMismatch{..}
    = case kActualS of
        Nothing -> "Expected sort `" <> pretty sExpected <> "` but got `" <> pretty sActual <> "`"
        Just k -> "Expected sort `" <> pretty sExpected <> "` for kind `" <> pretty k <> "` but actual sort is `" <> pretty sActual <> "`"

  msg KindError{..}
    = "Type `" <> pretty errTy
    <> "` does not have expected kind `" <> pretty errKL <> "`"

  msg KindCannotFormSet{..}
    = "Types of kind `" <> pretty errK <> "` cannot be used in a type-level set."

  msg KindsNotEqual{..}
    = "Kind `" <> pretty errK1 <> "` is not equal to `" <> pretty errK2 <> "`"

  msg IntervalGradeKindError{..}
   = "Interval grade mismatch `" <> pretty errTy1 <> "` and `" <> pretty errTy2 <> "`"

  msg LinearityError{..} = case linearityMismatch of
    LinearUsedMoreThanOnce v ->
      "Linear variable `" <> pretty v <> "` is used more than once."
    LinearNotUsed v ->
      "Linear variable `" <> pretty v <> "` is never used."
    LinearUsedNonLinearly v ->
      "Variable `" <> pretty v
      <> "` is promoted but its binding is linear; its binding should be under a box."
    NonLinearPattern ->
      "Wildcard pattern `_` allowing a value to be discarded"
    HandlerLinearityMismatch ->
      "Linearity of Handler clauses does not match"

  msg UniquenessError{..} = case uniquenessMismatch of
    NonUniqueUsedUniquely t ->
      "Cannot guarantee uniqueness of reference to value of type `" <> pretty t <> "`."
    UniquePromotion t ->
      "Cannot promote non-unique value of type `" <> pretty t <> "` to unique, since uniqueness is not a coeffect."

  msg UnpromotableError{..} = "Cannot promote a value of type `" <> pretty errTy <> "` in call-by-value mode."

  msg PatternTypingError{..}
    = "Pattern match `"
    <> pretty errPat
    <> "` does not have expected type `"
    <> pretty tyExpected
    <> "`"

  msg PatternTypingMismatch{..}
    = "Expected type `"
    <> pretty tyExpected
    <> "` but got `"
    <> pretty tyActual
    <> "` in pattern `"
    <> pretty errPat
    <> "`"

  msg PatternArityError{..}
    = "Data constructor `"
      <> pretty errId
      <> "` is applied to too many arguments."

  msg UnboundVariableError{..} = "`" <> pretty errId <> "`"

  msg UnboundTypeVariable{..}
    = "`" <> pretty errId <> "` is not quantified"

  msg RefutablePatternError{..}
    = "Pattern match " <> pretty errPat
    <> " can fail; only irrefutable patterns allowed in this context"

  msg TypeConstructorNameClash{..}
    = "Type constructor `" <> pretty errId <> "` already defined"

  msg DataConstructorTypeVariableNameClash{..} = mconcat
    [ "Type variable "
    , pretty errVar
    , " in data constructor `"
    , pretty errDataConstructorId
    , "` are already bound by the associated type constructor `"
    , pretty errTypeConstructor
    , "`. Choose different, unbound names."
    ]

  msg DuplicateBindingError { errLoc, duplicateBinding }
    = "Variable `" <> duplicateBinding <> "` bound more than once."

  msg UnificationError{..} = if pretty errTy1 == pretty errTy2
    then "Type `" <> pretty errTy1 <> "` is not unifiable with the type `" <> pretty errTy2 <> "` coming from a different binding"
    else "Type `" <> pretty errTy1 <> "` is not unifiable with the type `" <> pretty errTy2 <> "`"

  msg (OccursCheckFail _ var t) =
    "Type variable `" <> pretty var <> "` cannot be unified with type `"
        <> pretty t <> "` (occurs check failure; implies infinite type)."

  msg (UnificationKindError _ t1 k1 t2 k2)
    = "Trying to unify a type `"
    <> pretty t1 <> "` of kind " <> pretty k1
    <> " with a type `"
    <> pretty t2 <> "` of kind " <> pretty k2

  msg TypeVariableMismatch{..}
    = "Variable " <> pretty errVar <> " is being used at two conflicting types "
    <> "`" <> pretty errTy1 <> "` and `" <> pretty errTy2 <> "`"

  msg UndefinedEqualityError{..}
    = "Equality is not defined at kind "
    <> pretty errKL
    <> "\t\n from equality between "
    <> "'" <> pretty errTy2 <> "' and '" <> pretty errTy1 <> "' equal."

  msg CoeffectUnificationError{..}
    = "Cannot unify coeffect types '"
    <> pretty errTy1 <> "' and '" <> pretty errTy2
    <> "' for coeffects `" <> pretty errC1 <> "` and `" <> pretty errC2 <> "`"

  msg DataConstructorNameClashError{..}
    = "Data constructor `" <> pretty errId <> "` already defined."

  msg EffectMismatch{..}
    = "Expected `" <> pretty effExpected
    <> "`, but got `" <> pretty effActual <> "`"

  msg UnificationDisallowed{..}
    = "Trying to unify `"
    <> pretty errTy1 <> "` and `"
    <> pretty errTy2 <> "` but in a context where unification is not allowed."

  msg UnificationFailGeneric{..}
    = "Trying to unify `" <> pretty errSubst1 <> "` and `" <> pretty errSubst2 <> "`"

  msg UnificationFail{..}
    = "Cannot unify universally quantified type variable `" <> pretty errVar
    <> "` of kind `" <> pretty errKind <> "` with " <> (if tyIsConcrete then "a concrete type " else "") <> "`" <> pretty errTy <> "`"

  msg SessionDualityError{..}
    = "Session type `" <> pretty errTy1 <> "` is not dual to `" <> pretty errTy2 <> "`"

  msg (NoUpperBoundError _ errTy1 errTy2)
    = "Types `" <> pretty errTy1 <> "` and `"
    <> pretty errTy2 <> "` have no upper bound"

  msg DisallowedCoeffectNesting{..}
    = "Graded modalities of outer index type `" <> pretty errTyOuter
    <> "` and inner type `" <> pretty errTyInner <> "` cannot be nested"

  msg UnboundDataConstructor{..}
    = "`" <> pretty errId <> "`"

  msg UnboundTypeConstructor{..}
    = "`" <> pretty errId <> "`"

  msg TooManyPatternsError{..}
    = "Couldn't match expected type `"
    <> pretty tyExpected
    <> "` against a type of the form `"
    <> pretty tyActual
    <> "` implied by the remaining pattern(s)\n\t"
    <> (intercalate "\n\t" . map (ticks . pretty) . toList) errPats

  msg DataConstructorReturnTypeError{..}
    = "Expected type constructor `" <> pretty idExpected
    <> "`, but got `" <> pretty idActual <> "`"

  msg MalformedDataConstructorType{..}
    = "`" <> pretty errTy <> "` not valid in a data constructor definition"

  msg ExpectedEffectType{..}
    = "Expected a type of the form `a <eff>` but got `"
    <> pretty errTy

  msg ExpectedOptionalEffectType{..}
    = "Expected a type of the form `a <eff>[0..1]` but got `"
    <> pretty errTy

  msg LhsOfApplicationNotAFunction{..}
    = "Expected a function type on the left-hand side of an application, but got `"
    <> pretty errTy <> "`"

  msg FailedOperatorResolution{..}
    = "Could not resolve operator `" <> pretty errOp
    <> "` at type `" <> pretty errTy <> "`"

  msg NeedTypeSignature{..}
    = "The type could not be inferred, please add a type signature to expression `"
    <> pretty errExpr <> "`"

  msg SolverErrorCounterExample{..}
    =  prettyNegPred errDefId errPred
    <> (if null message then "" else "\n\n" <> message)

  msg SolverErrorFalsifiableTheorem{..}
    =  prettyNegPred errDefId errPred

  msg SolverError{..} = errMsg <> " for theorem:\n\t" <> pretty errPred

  msg SolverTimeout{errSolverTimeoutMillis, errDefId, errContext, errPred}
    = "Solver timed out with limit of " <> show errSolverTimeoutMillis
    <> "ms while checking the " <> errContext <> " of definition `" <> pretty errDefId
    <> "` with the following theorem:\n"
    <> pretty errPred
    <> "\nYou may want to increase the timeout (see --help)."

  msg UnifyGradedLinear{..}
    = "Variable `" <> pretty errLinearOrGraded
    <> "` is used as graded variable, but it is bound as a linear variable."

  msg ImpossiblePatternMatch{ errId, errPred }
    = "Pattern match in an equation of `" <> pretty errId
    <> "` is impossible as it implies the unsatisfiable condition "
    <> pretty errPred

  msg ImpossiblePatternMatchTrivial{ errId, errUnsats }
    = "Pattern match in an equation of `" <> pretty errId
    <> "` is impossible as it implies the unsatisfiable condition "
    <> unlines (map pretty errUnsats)

  msg NameClashTypeConstructors{..}
    = "`" <> pretty (dataDeclId errDataDecl) <> "` already defined at\n\t"
    <> (intercalate "\n\t" . map (pretty . dataDeclSpan) . toList) otherDataDecls

  msg NameClashDataConstructors{..}
    = "`" <> pretty (dataConstrId errDataConstructor) <> "` already defined at\n\t"
    <> (intercalate "\n\t" . map (pretty . dataConstrSpan) . toList) otherDataConstructors

  msg NameClashDefs{..}
    = "`" <> pretty (defId errDef) <> "` already defined at\n\t"
    <> (intercalate "\n\t" . map (pretty . defSpan) . toList) otherDefs

  msg UnexpectedTypeConstructor{ tyConActual, tyConExpected }
    = "Expected type constructor `" <> pretty tyConExpected
               <> "`, but got `" <> pretty tyConActual <> "`"

  msg InvalidTypeDefinition{ errTy }
    = "The type `" <> pretty errTy <> "` is not valid in a datatype definition."

  msg InvalidHolePosition{} = "Hole occurs in synthesis position so the type is not yet known"

  msg UnknownResourceAlgebra{ errK, errTy }
    = "There is no resource algebra defined for `" <> pretty errK <> "`, arising from effect term `" <> pretty errTy <> "`"

  msg CaseOnIndexedType{ errTy }
    = "Cannot use a `case` pattern match on indexed type " <> pretty errTy <> ". Define a specialised function instead."

  msg OperatorUndefinedForKind{ errK, errTyOp }
    = "Operator " <> pretty errTyOp <> " is not defined for type-level terms of kind " <> pretty errK

  msg (WrongLevel _ errTy l')
    = "Type `" <> pretty errTy <> "`"
     <> " but it is trying to be used at a level " <> pretty l' <> " setting."

  msg ImpossibleKindSynthesis{ errTy }
    = "Cannot synthesise a kind for `" <> pretty errTy <> "`"

  msg NaturalNumberAtWrongKind{ errTy, errK }
    = "Natural number `" <> pretty errTy <> "` is not a member of `" <> pretty errK <> "`"

  msg InvalidPromotionError{ errTy }
    = "Invalid promotion of closed term to `" <> pretty errTy <> "`"

  msg TypeConstraintNotSatisfied{ errTy }
    = "Constraint `" <> pretty errTy <> "` does not hold or is not provided by the type constraint assumptions here."

  color HoleMessage{} = Blue
  color _ = Red


data LinearityMismatch
  = LinearNotUsed Id
  | LinearUsedNonLinearly Id
  | NonLinearPattern
  | LinearUsedMoreThanOnce Id
  | HandlerLinearityMismatch
  deriving (Eq, Show) -- for debugging

data UniquenessMismatch
  = NonUniqueUsedUniquely Type
  | UniquePromotion Type
  deriving (Eq, Show)

freshenPred :: Pred -> Checker Pred
freshenPred pred = do
    st <- get
    -- Run the freshener using the checkers unique variable id
    let (pred', freshenerState) =
         runIdentity $ runStateT (freshen pred)
          (FreshenerState { counter = 1 + uniqueVarIdCounter st, varMap = [], tyMap = []})
    -- Update the unique counter in the checker
    put (st { uniqueVarIdCounter = counter freshenerState })
    return pred'

-- help to get a map from type constructor names to a map from data constructor names to their types and subst
getDataConstructors :: Id -> Checker (Maybe (Ctxt (TypeScheme, Substitution)))
getDataConstructors tyCon = do
  st <- get
  let tyCons   = typeConstructors st
  let dataCons = dataConstructors st
  return $
    case lookup tyCon tyCons of
      Just (k, dataConsNames, _) ->
          case resultType k of
            Type _ ->
              Just $ mapMaybe (\dataCon -> lookup dataCon dataCons >>= (\x -> return (dataCon, x))) dataConsNames
            _ ->
              -- Ignore not Type thing
              Nothing
      Nothing -> Nothing
