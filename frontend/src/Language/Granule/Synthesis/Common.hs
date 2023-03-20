module Language.Granule.Synthesis.Common where

import Language.Granule.Context
import Language.Granule.Checker.Monad
          (allDataConstructorNames,predicateContext,tyVarContext,uniqueVarIdCounterMap
          ,predicateStack,resetAddedConstraintsFlag
          ,Assumption(..))
import Language.Granule.Checker.CoeffectsTypeConverter
import Language.Granule.Checker.Constraints
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Kinding
  (combineSubstitutions)
import Language.Granule.Checker.Substitution
  (substitute, freshPolymorphicInstance)
import Language.Granule.Checker.SubstitutionContexts
  (Substitution,flipSubstitution)
import Language.Granule.Checker.Types
  (equalTypes)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Synthesis.Monad
import Language.Granule.Synthesis.Contexts
import Language.Granule.Utils

import qualified Data.Map as M
import qualified System.Clock as Clock
import Control.Monad.State.Strict(modify,lift,liftIO,get,put)

-- # Key data types for controlling synthesis

data PruningScheme = NonPruning | Pruning
  deriving (Show, Eq)

data ResourceScheme a = Additive a | Subtractive
  deriving (Show, Eq)

-- Augments a standard Granule assumption with StructInfo
-- (if applicable to theassumptions type).

data Goal = Goal TypeScheme (Maybe StructInfo)
  deriving (Show, Eq)

-- UNDER REVIEW: are seperate counters for intros and elims really neccessary?
data Depth = Depth
  {
    elims     :: Int -- Maximum number of eliminations (of recursive data structures) allowed
  , intros    :: Int -- Maximum number of introductions (of recursive data structures) allowed
  , iCurrent  :: Int -- Current level of introductions performed
  }
  deriving (Show, Eq)

-- Phases of focusing, in brief:
-- * Right Async: (initial phase) introduction rule abstraction, when abs
--                rule can no longer be applied, tranasition to:
-- * Left Async: elimination rules for constructors and graded modalities
--               when these are all decomposed, transition to focusing where
--               one of the sync phases is chosen:
-- * Right Sync: constructor and graded modality introductions. Transitions back
--               Right Async when finished.
-- * Left Sync:  applications and variables.
data FocusPhase = RightAsync | RightSync | LeftAsync | LeftSync

-- Represents a renaming for the purposes of
-- pushing a fresh variable name from an unboxing up to
-- the outer expression for refactoring e.g.:
--
-- let [x] = y : A in x
--
-- yields the binding  [(y, (x, A))] which allows the let binding to
-- later be refactored to:
--
-- f [x] = x
--
type Bindings = Ctxt (Id, Type)

-- Search parameters

data SearchParameters =
  SearchParams {
    scrutCurrent  :: Integer
  , scrutMax      :: Integer
  , matchCurrent  :: Integer
  , matchMax      :: Integer
  , guessCurrent  :: Integer
  , guessMax      :: Integer
  }
  deriving (Show, Eq)

defaultSearchParams :: SearchParameters
defaultSearchParams =
  SearchParams {
    scrutCurrent = 0
  , scrutMax = 1
  , matchCurrent = 0
  , matchMax = 0
  , guessCurrent = 0
  , guessMax = 18
    }


incrG :: SearchParameters -> SearchParameters
incrG sParams = sParams { guessCurrent = (guessCurrent sParams) + 1}

-- # Key focusing characterisation functions

-- Right Asynchronous
isRAsync :: Type -> Bool
isRAsync FunTy{} = True
isRAsync _       = False

-- Right Synchronous
isRSync :: Type -> Bool
isRSync TyApp{} = True
isRSync TyCon{} = True
isRSync Box{}   = True
isRSync _       = False

-- Left Asynchronous
isLAsync :: Type -> Bool
isLAsync TyApp{} = True
isLAsync TyCon{} = True
isLAsync Box{}   = True
isLAsync _       = False

-- Left Synchronous
isLSync :: Type -> Bool
isLSync FunTy{} = True
isLSync _       = False

-- TODO: would something like the following be useful
-- for using with `bindToContext`?
-- Determine focus phase for a type
-- focusPhase :: Type -> FocusPhase
-- focusPhase t | isLAsync t = LeftAsync
-- focusPhase t | otherwise  = error "TODO"

-- # Helpers

-- ## AST

ns :: Span
ns = nullSpanNoFile

-- TODO: is this the right name?
-- Is the unit type atomic?
isAtomic :: Type -> Bool
isAtomic TyVar {} = True
isAtomic _ = False

-- TODO: this feels misnamed...
-- If the type is an ADT or GADT, return the TyCon name
isADTorGADT :: Type -> Maybe Id
isADTorGADT (TyCon id) = Just id
isADTorGADT (TyApp e1 e2) = isADTorGADT e1
isADTorGADT _ = Nothing

-- Compare the arity of two type schemes for data constructors
compareArity :: (Id, (TypeScheme, Substitution))
             -> (Id, (TypeScheme, Substitution))
             -> Ordering
compareArity con1@(_, (Forall _ _ _ ty1, _)) con2@(_, (Forall _ _ _ ty2, _)) =
  compare (arity ty1) (arity ty2)

-- Generate a fresh identifier
freshIdentifier :: Synthesiser Id
freshIdentifier = do
  let mappo = ["x","y","z","u","v","w","p","q"]
  let base = "x"
  checkerState <- get
  let vmap = uniqueVarIdCounterMap checkerState
  case M.lookup base vmap of
    Nothing -> do
      let vmap' = M.insert base 1 vmap
      put checkerState { uniqueVarIdCounterMap = vmap' }
      return $ mkId base

    Just n -> do
      let vmap' = M.insert base (n+1) vmap
      put checkerState { uniqueVarIdCounterMap = vmap' }
      let n' = fromInteger . toInteger $ n
      if n' < length mappo
        then return $ mkId $ mappo !! n'
        else return $ mkId $ base <> show n'

-- Given an optional binder name, either give the binder name back
-- or generate a fresh variable
useBinderNameOrFreshen :: Maybe Id -> Synthesiser Id
useBinderNameOrFreshen Nothing  = freshIdentifier
useBinderNameOrFreshen (Just n) = return n

getSAssumptionType :: (?globals :: Globals) =>
  SAssumption -> Synthesiser (Type, Bool, Maybe Type, Maybe StructInfo, TypeScheme)
getSAssumptionType (SVar (Linear t) sInfo) = return (t, False, Nothing, sInfo, Forall ns [] [] t)
getSAssumptionType (SVar (Discharged t g) sInfo) = return (t, False, Just g, sInfo, Forall ns [] [] t)
getSAssumptionType (SDef tySch usage) = do
  -- If this is a top level definition, we should freshen it
  (freshTy, tyVarsFreshD, substFromFreshening, constraints', _) <- conv $ freshPolymorphicInstance InstanceQ False tySch [] []
  return $ (freshTy, True, usage, Nothing, tySch)
getSAssumptionType (SVar (Ghost _) sInfo) =
  error "Cannot synthesis in the context of Ghost variables (i.e., for language SecurityLevels)"

-- ## Typing

-- TODO: refactor this to take the FocusPhase instead
-- of a boolean?
bindToContext ::
     (Id, SAssumption)    -- The assumption being bound
  -> Ctxt SAssumption     -- Gamma
  -> Ctxt SAssumption     -- Omega
  -> Bool                  -- is Left Asynchronous?
  -> (Ctxt SAssumption, Ctxt SAssumption)
bindToContext var gamma omega True = (gamma, var:omega)
bindToContext var gamma omega _         = (var:gamma, omega)



isRecursiveType :: Type -> Ctxt (Ctxt (TypeScheme, Substitution), Bool) -> Bool 
isRecursiveType t tyConstrs = 
  case isADTorGADT t of 
    Just name -> 
      case lookup name tyConstrs of 
        Just (dataCons, recursive) -> recursive
        Nothing -> False
    _ -> False 

-- Given inputs:
-- `isRecursiveCon dataTypeName (dataConstructorName, (dataConstrType,  coercions))`
-- determine if `dataConstructorName` is a data constructor that constructs a
-- recursive type instance
-- e.g., for `data List a = Nil | Cons a (List a)`
-- then `isRecursiveCons "List" ("Cons", ..type-of-cons..) = True
-- but  `isRecursiveCons "List" ("Nil", ..type-of-cons..) = False
isRecursiveCon :: Id -> (Id, (TypeScheme, Substitution)) -> Bool
isRecursiveCon tyConId (_, (Forall _ _ _ constructorTy, subst)) =
  any (positivePosition tyConId) (parameterTypes constructorTy)


-- Determine if type constructor `tyConId` appears
-- in a positive (recursive) position in a type
positivePosition :: Id -> Type -> Bool
positivePosition tyConId (TyCon id)      = (tyConId == id)
positivePosition id (TyApp t1 t2)   = positivePosition id t1 || positivePosition id t2
positivePosition id (FunTy _ _ _ t) = positivePosition id t
positivePosition id (Box _ t)       = positivePosition id t
positivePosition id (Diamond _ t)   = positivePosition id t
positivePosition id (Star _    t)   = positivePosition id t
positivePosition id (TyVar _)       = False
positivePosition id (TyInt _)       = False
positivePosition id (TyRational _)  = False
positivePosition id (TyGrade _ _)   = False
positivePosition id (TyInfix _ t1 t2) = positivePosition id t1 || positivePosition id t2
positivePosition id (TySet _ t)       = any (positivePosition id) t
positivePosition id (TyCase t ts)     = positivePosition id t || any (positivePosition id . snd) ts
positivePosition id (TySig t _)       = positivePosition id t
positivePosition id (Type  _)         = False

isDecreasing :: Id -> [Type] -> Bool
isDecreasing id1 [] = False
isDecreasing id1 ((TyCon id2):tys) = (id1 == id2) || isDecreasing id1 tys
isDecreasing id1 ((Box _ t):tys)   = isDecreasing id1 (t:tys)
isDecreasing id1 ((FunTy _ _ t1 t2):tys) = isDecreasing id1 (t1:t2:tys)
isDecreasing id1 ((TyApp t1 t2):tys)   = isDecreasing id1 (t1:t2:tys)
isDecreasing id1 (x:xs) = isDecreasing id1 xs

-- # Common synthesis helpers

-- Takes a data constructor and returns whether the constructor is a canditate for synthesis based on
-- the type of the assumption. If so, return a fresh polymorphic instance of that constructor.
checkConstructor :: (?globals::Globals)
      => TypeScheme       -- Type of data type definition
      -> Type             -- Type of assumption
      -> Substitution
      -> Synthesiser (Bool, Type, [(Type, Maybe Coeffect)], Substitution, Substitution, Pred)
checkConstructor con@(Forall  _ binders constraints conTy) assumptionTy subst = do
    conv $ resetAddedConstraintsFlag -- reset the flag that says if any constraints were added
    -- Generate a fresh instance of this constructor (assumes it is not indexed)
    let typeIndices = []
    (conTyFresh, tyVarsFreshD, substFromFreshening, constraints', coercions) <-
        conv $ freshPolymorphicInstance InstanceQ True con subst typeIndices

    -- Take the rightmost type of the function type, collecting the arguments along the way
    let (conTy', args) = collectTyAndArgs conTyFresh
    -- Apply the coercions associated with this data constructor
    conTy'' <- conv $ substitute coercions conTy'

    -- Check if assumptionTy == conTy?
    (success, specTy, subst') <- conv $ equalTypes ns assumptionTy conTy''

    -- TODO: reconsider the flip here
    subst'' <- conv $ combineSubstitutions ns (flipSubstitution coercions) subst'

    -- Take the constraints generated by the type equality and add these to the synthesis predicate
    cs <- conv $ get
    let predicate = Conj $ predicateStack cs
    -- Clear the checker state predicate
    conv $ modify (\s -> s { predicateStack = []})
    return (success, specTy, args, subst'', substFromFreshening, predicate)

  where
  -- | Get the right most of a function type and collect its arguments in a list
  collectTyAndArgs :: Type -> (Type, [(Type, Maybe Coeffect)])
  collectTyAndArgs (FunTy _ coeff arg t) = let (t', args) = collectTyAndArgs t in (t', (arg, coeff) : args)
  collectTyAndArgs t = (t, [])

-- Return constructors relevant to the type constructor ID in two lists: recursive and non-recursive
relevantConstructors :: Id
 -> Ctxt (Ctxt (TypeScheme, Substitution), Bool)
 -> (Ctxt ((TypeScheme, Substitution)), Ctxt ((TypeScheme, Substitution)))
relevantConstructors id [] = ([], [])
relevantConstructors id ((typeId, (dCons, _)):tys) =
  if id == typeId then
    let (recCons, nonRecCons) = relevantConstructors id tys in
      let (recCons', nonRecCons') = relevantConstructors' id dCons in
        (recCons ++ recCons', nonRecCons ++ nonRecCons')
  else
    relevantConstructors id tys
  where
    relevantConstructors' id [] = ([], [])
    relevantConstructors' id (dCon:dCons) =
      let (recCons, nonRecCons) = relevantConstructors' id dCons in
        if isRecursiveCon id dCon then
          (dCon:recCons, nonRecCons)
        else
          (recCons, dCon:nonRecCons)

-- Call the solver on the internally generated predicate and get boolean result
solve :: (?globals :: Globals) => Synthesiser Bool
solve = do
  cs <- conv get

  tyVars <- conv $ includeOnlyGradeVariables ns (tyVarContext cs)

  let pred = fromPredicateContext (predicateContext cs)

  -- Prove the predicate
  start  <- liftIO $ Clock.getTime Clock.Monotonic
  constructors <- conv allDataConstructorNames
  (smtTime', result) <- liftIO $ provePredicate pred tyVars constructors
  -- Force the result
  _ <- return result
  end    <- liftIO $ Clock.getTime Clock.Monotonic
  let proveTime' = fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double)
  -- Update benchmarking data
  Synthesiser $ lift $ lift $ lift $ modify (\state ->
            state {
             smtCallsCount = 1 + smtCallsCount state,
             smtTime = smtTime' + smtTime state,
             proveTime = proveTime' + proveTime state,
             theoremSizeTotal = toInteger (length tyVars) + sizeOfPred pred + theoremSizeTotal state
                  })

  case result of
    QED -> do
      debugM "synthDebug" "SMT said: Yes."
      return True
    NotValid s -> do
      debugM "synthDebug" "SMT said: No."
      return False
    SolverProofError msgs ->
      return False
    OtherSolverError reason ->
      return False
    Timeout -> do
      debugM "synthDebug" "SMT said: Timeout."
      return False
    _ ->
      return False

-- ## Size calculations on predicates, constraints, and grades

sizeOfPred :: Pred -> Integer
sizeOfPred (Conj ps) = 1 + sum (map sizeOfPred ps)
sizeOfPred (Disj ps) = 1 + sum (map sizeOfPred ps)
sizeOfPred (Impl binders p1 p2) = 1 + toInteger (length binders) + sizeOfPred p1 + sizeOfPred p2
sizeOfPred (Con c) = sizeOfConstraint c
sizeOfPred (NegPred p) = 1 + sizeOfPred p
sizeOfPred (Exists _ _ p) = 1 + sizeOfPred p

sizeOfConstraint :: Constraint -> Integer
sizeOfConstraint (Eq _ c1 c2 _) = 1 + sizeOfCoeffect c1 + sizeOfCoeffect c2
sizeOfConstraint (Neq _ c1 c2 _) = 1 + sizeOfCoeffect c1 + sizeOfCoeffect c2
sizeOfConstraint (ApproximatedBy _ c1 c2 _) = 1 + sizeOfCoeffect c1 + sizeOfCoeffect c2
sizeOfConstraint (Hsup _ c1 c2 _) = 1 + sizeOfCoeffect c1 + sizeOfCoeffect c2
sizeOfConstraint (Lub _ c1 c2 c3 _) = 1 + sizeOfCoeffect c1 + sizeOfCoeffect c2 + sizeOfCoeffect c3
sizeOfConstraint (Lt _ c1 c2) = 1 + sizeOfCoeffect c1 + sizeOfCoeffect c2
sizeOfConstraint (Gt _ c1 c2) = 1 + sizeOfCoeffect c1 + sizeOfCoeffect c2
sizeOfConstraint (LtEq _ c1 c2) = 1 + sizeOfCoeffect c1 + sizeOfCoeffect c2
sizeOfConstraint (GtEq _ c1 c2) = 1 + sizeOfCoeffect c1 + sizeOfCoeffect c2

sizeOfCoeffect :: Type -> Integer
sizeOfCoeffect (TyInfix _ c1 c2) = 1 + sizeOfCoeffect c1 + sizeOfCoeffect c2
sizeOfCoeffect (TyGrade _ _) = 0
sizeOfCoeffect (TyInt _) = 0
sizeOfCoeffect (TyVar _) = 0
sizeOfCoeffect _ = 0