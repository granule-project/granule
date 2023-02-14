{-# LANGUAGE ImplicitParams #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}


{-# options_ghc -fno-warn-incomplete-uni-patterns #-}
module Language.Granule.Synthesis.Synth where

import qualified Data.Map as M

import Data.List (sortBy,nub) 

import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
-- import Control.Monad.Logic
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span

import Language.Granule.Context

import Language.Granule.Checker.CoeffectsTypeConverter
import Language.Granule.Checker.Constraints
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Kinding
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Types
import Language.Granule.Synthesis.Builders
import Language.Granule.Synthesis.Monad
import Language.Granule.Synthesis.Contexts

import Data.Either (rights)
import Control.Monad.State.Strict

import qualified Control.Monad.State.Strict as State (get)
import qualified System.Clock as Clock
-- import qualified Control.Monad.Memo as Memo
import qualified System.Timeout
import qualified Data.List.Ordered as Ordered

import Language.Granule.Utils
import Data.Maybe (fromJust, catMaybes, fromMaybe)
import Control.Arrow (second)
-- import Control.Monad.Omega
import System.Clock (TimeSpec)

import Data.Ord


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

-- Augments a standard Granule assumption with StructInfo (if applicable to the 
-- assumptions type).

data Goal =  Goal TypeScheme (Maybe StructInfo)
  deriving (Show, Eq)

data PruningScheme = NonPruning | Pruning
  deriving (Show, Eq)

data ResourceScheme a = Additive a | Subtractive
  deriving (Show, Eq)


-- Pushes the fresh variable name from an unboxing up to the outer expression 
-- for refactoring e.g.: 
-- let [x] = y : A in x 
-- yields the binding  [(y, (x, A))] which allows the let binding to 
-- later be refactored to: 
-- f [x] = x
type Bindings = [(Id, (Id, Type))]



-- UNDER REVIEW: are seperate counters for intros and elims really neccessary?
data Depth = Depth 
  {
    elims    :: Int    -- Maximum number of eliminations (of recursive data structures) allowed
  , intros    :: Int   -- Maximum number of introductions (of recursive data structures) allowed
  , iCurrent   :: Int  -- Current level of introductions performed
  }
  deriving (Show, Eq)


------------------------------

-- Additional semiring-dependent constraints for additive resource management.
-- If we are in additive mode, we can finish early if such a constraint is not 
-- satisfiable:
-- 
-- ∀x,y . x ⊑︎ y => xRy
--  
increasingConstraints :: (?globals :: Globals) => Ctxt SAssumption -> Ctxt SAssumption -> Synthesiser ()
increasingConstraints gamma delta = increasingConstraints' gamma delta False
  where 
    increasingConstraints' [] delta addedConstraints = do 
      res <- if addedConstraints then solve else return True
      boolToSynthesiser res ()
    increasingConstraints' (gVar@(name, SVar (Discharged _ grade) _):gamma) delta addedConstraints = 
      case lookup name delta of 
        Just (SVar (Discharged _ grade') _) -> do 
          (kind, _, _) <- conv $ synthKind ns grade
          addIncreasingConstraint kind grade grade'
          increasingConstraints' gamma delta True
        _ -> increasingConstraints' gamma delta addedConstraints
  

addIncreasingConstraint :: Kind -> Type -> Type -> Synthesiser ()
addIncreasingConstraint k@(isInterval -> Just t) gradeIn gradeOut = do 
  st <- conv get
  var <- freshIdentifier
  conv $ existentialTopLevel var k
  liftIO $ putStrLn $ "gradeIn: " <> show gradeIn
  liftIO $ putStrLn $ "gradeOut: " <> show gradeOut
  modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyInfix TyOpPlus gradeOut (TyVar var)) gradeIn k) (predicateContext st)

addIncreasingConstraint k@(TyCon con) gradeIn gradeOut  = 
  case internalName con of 

    -- Natural Numbers: R = {(x, y) | ∃z. x + z ⊑ y} 
    "Nat" -> do 
      st <- conv get
      var <- freshIdentifier
      conv $ existentialTopLevel var k
      liftIO $ putStrLn $ "gradeIn: " <> show gradeIn
      liftIO $ putStrLn $ "gradeOut: " <> show gradeOut
      modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyInfix TyOpPlus gradeOut (TyVar var)) gradeIn k) (predicateContext st)

    -- Linear/Non Linear: R = {(x, y) | } 
    "LNL" -> do
      st <- conv get
      var <- freshIdentifier
      conv $ existentialTopLevel var k
      liftIO $ putStrLn $ "gradeIn: " <> show gradeIn
      liftIO $ putStrLn $ "gradeOut: " <> show gradeOut
      modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyInfix TyOpPlus gradeOut (TyVar var)) gradeIn k) (predicateContext st)

    -- TBD
    "Level" -> return ()
    "Borrowing" -> return ()
    "OOZ" -> return ()
addIncreasingConstraint _ _ _ = return ()

ns :: Span 
ns = nullSpanNoFile


solve :: (?globals :: Globals) => Synthesiser Bool
solve = do
  cs <- conv State.get
  tyVars <- conv $ includeOnlyGradeVariables ns (tyVarContext cs)

  st <- conv get 

  let pred = fromPredicateContext (predicateContext st)
  debugM "synthDebug" ("SMT on pred = " ++ pretty pred)

  -- Prove the predicate
  start  <- liftIO $ Clock.getTime Clock.Monotonic
  constructors <- conv allDataConstructorNames
  (smtTime', result) <- liftIO $ provePredicate pred tyVars constructors
  -- Force the result
  _ <- return result
  end    <- liftIO $ Clock.getTime Clock.Monotonic
  let proverTime' = fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double)
  -- Update benchmarking data
  Synthesiser $ lift $ lift $ lift $ modify (\state ->
            state {
             smtCallsCount = 1 + smtCallsCount state,
             smtTime = smtTime' + smtTime state,
             proverTime = proverTime' + proverTime state,
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





bindToContext :: 
     (Id, SAssumption)    -- The assumption being bound
  -> Ctxt SAssumption     -- Gamma
  -> Ctxt SAssumption     -- Omega 
  -> Bool                 -- is Left Asynchronous? 
  -> (Ctxt SAssumption, Ctxt SAssumption)
bindToContext var gamma omega True = (gamma, var:omega)
bindToContext var gamma omega False = (var:gamma, omega)

-- If the type is an ADT or GADT, return the TyCon name
isADTorGADT :: Type -> Maybe Id
isADTorGADT (TyCon id) = Just id
isADTorGADT (TyApp e1 e2) = isADTorGADT e1
isADTorGADT _ = Nothing


-- Right Asynchronous
isRAsync :: Type -> Bool
isRAsync FunTy{} = True
isRAsync _ = False

-- Right Synchronous
isRSync :: Type -> Bool
isRSync TyApp{} = True
isRSync TyCon{} = True
isRSync Box{}   = True
isRSync _ = False

-- Left Asynchronous
isLAsync :: Type -> Bool
isLAsync TyApp{} = True
isLAsync TyCon{} = True
isLAsync Box{}   = True
isLAsync _ = False

-- Left Synchronous
isLSync :: Type -> Bool
isLSync FunTy{} = True
isLSync _ = False

-- TyVars
isAtomic :: Type -> Bool
isAtomic TyVar {} = True
isAtomic _ = False


-- TODO: rewrite a lot of checkConstructor and auxilliary functions

-- Takes a data constructor and returns whether the constructor is a canditate for synthesis based on
-- the type of the assumption. If so, return a fresh polymorphic instance of that constructor. 
checkConstructor :: (?globals::Globals)
      => Bool             -- Do impossibility check?
      -> TypeScheme       -- Type of data type definition 
      -> Type             -- Type of assumption
      -> Substitution     
      -> Synthesiser (Bool, Type, [(Type, Maybe Coeffect)], Substitution, Substitution)
checkConstructor impossibility con@(Forall  _ binders constraints conTy) assumptionTy subst = do
    conv $ resetAddedConstraintsFlag -- reset the flag that says if any constraints were added
    (conTyFresh, tyVarsFreshD, substFromFreshening, constraints', coercions) <- conv $ freshPolymorphicInstance InstanceQ True con subst 

    -- Take the rightmost type of the function type, collecting the arguments along the way 
    let (conTy', args) = collectTyAndArgs conTyFresh
    conTy'' <- conv $ substitute coercions conTy'

    -- assumptionTy == conTy?
    (success, specTy, subst') <- conv $ equalTypes ns assumptionTy conTy''
 
    st <- getSynthState
    cs <- conv $ get

    -- Take the constraints generated by the type equality and add these to the synthesis predicate
    modifyPred $ addPredicateViaConjunction (Conj $ predicateStack cs) (predicateContext cs)
    
    -- Clear the checker state predicate
    conv $ modify (\s -> s { predicateStack = []}) 


    if impossibility && addedConstraints cs && success then do
      res <- solve
      return (res, specTy, args, subst', substFromFreshening)
    else 
      return (success, specTy, args, subst', substFromFreshening)

  where 
  -- | Get the right most of a function type and collect its arguments in a list
  collectTyAndArgs :: Type -> (Type, [(Type, Maybe Coeffect)])
  collectTyAndArgs (FunTy _ coeff arg t) = let (t', args) = collectTyAndArgs t in (t', ((arg, coeff) : args))
  collectTyAndArgs t = (t, [])

compareArity :: (Id, (TypeScheme, Substitution)) -> (Id, (TypeScheme, Substitution)) -> Ordering
compareArity con1@(_, (Forall _ _ _ ty1, _)) con2@(_, (Forall _ _ _ ty2, _)) = compare (arity ty1) (arity ty2)

-- Return constructors relevant to the type constructor ID in two lists: recursive and non-recursive
relevantConstructors :: Id -> Ctxt (Ctxt (TypeScheme, Substitution), Bool) -> (Ctxt ((TypeScheme, Substitution)), Ctxt ((TypeScheme, Substitution)))
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

markRecursiveType :: Id -> Type -> Bool
markRecursiveType tyCon dataTy = markRecursiveType' tyCon dataTy False
  where 
    markRecursiveType' tyCon (FunTy _ _ t1 t2) onLeft = do
      case markRecursiveType' tyCon t1 True of
        True -> True
        False -> markRecursiveType' tyCon t2 onLeft
    markRecursiveType' tyCon (TyApp t1 t2) True = do
      case markRecursiveType' tyCon t1 True of 
        True -> True
        False -> markRecursiveType' tyCon t2 True
    markRecursiveType' tyCon (TyCon tyCon') True = tyCon == tyCon' 
    markRecursiveType' _ _ _ = False


isRecursiveType :: Maybe Id -> Ctxt (Ctxt (TypeScheme, Substitution), Bool) -> Bool 
isRecursiveType (Just id) cons = case lookup id cons of Just (_, isRecursive)  -> isRecursive ; Nothing -> False
isRecursiveType _ _ = False


isRecursiveCon :: Id -> (Id, (TypeScheme, Substitution)) -> Bool
isRecursiveCon id1 (_, (Forall _ _ _ conTy, subst)) =
  case constrArgIds conTy of 
    Nothing -> False
    Just [] -> False
    Just args -> isDecreasing id1 args
  where   
    constrArgIds :: Type -> Maybe [Type]
    constrArgIds (TyCon id) = Just [TyCon id]
    constrArgIds (TyVar id) = Just [TyVar id]
    constrArgIds (Box _ t) = do 
      res <- constrArgIds t
      return res 
    constrArgIds (TyApp t1 t2) = do 
      res <- constrArgIds t2
      return $ t1 : res
    constrArgIds (FunTy _ _ e1 e2) = do
      res <- constrArgIds e2
      return $ e1 : res
    constrArgIds _ = Nothing


isDecreasing :: Id -> [Type] -> Bool
isDecreasing id1 [] = False 
isDecreasing id1 ((TyCon id2):tys) = if id1 == id2 then True else isDecreasing id1 tys
isDecreasing id1 ((Box _ t):tys)   = isDecreasing id1 (t:tys)
isDecreasing id1 ((FunTy _ _ t1 t2):tys) = isDecreasing id1 (t1:t2:tys) 
isDecreasing id1 ((TyApp t1 t2):tys)   = isDecreasing id1 (t1:t2:tys)
isDecreasing id1 (x:xs) = isDecreasing id1 xs




-- Note that the way this is used, the (var, assumption) pair in the first
-- argument is not contained in the provided context (second argument)
useVar :: (?globals :: Globals)
  => (Id, SAssumption)
  -> Ctxt SAssumption 
  -> ResourceScheme PruningScheme
  -> Maybe Type -- Grade-on-rule mode
  -> Synthesiser (Ctxt SAssumption)

-- Subtractive
useVar (name, SVar (Linear t) _) gamma Subtractive _ = return gamma
useVar (name, SVar (Discharged t grade) sInfo) gamma Subtractive Nothing = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  var <- freshIdentifier 
  conv $ existentialTopLevel var kind -- Existentials must be at the topLevel because they may be generated inside an implication but may occur outside of the implication 
  st <- conv get
  modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyInfix TyOpPlus (TyVar var) (TyGrade (Just kind) 1)) grade kind) (predicateContext st)
  res <- solve
  boolToSynthesiser res (replace gamma name (SVar (Discharged t (TyVar var)) sInfo))

--Subtractive Grade-on-Rule
useVar (name, SVar (Discharged t grade) sInfo) gamma Subtractive (Just gradeOnRule) = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  var <- freshIdentifier
  conv $ existentialTopLevel var kind
  st <- conv get
  modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyInfix TyOpPlus (TyVar var) gradeOnRule) grade kind) (predicateContext st)
  res <- solve
  boolToSynthesiser res (replace gamma name (SVar (Discharged t (TyVar var)) sInfo))

-- Additive
useVar (name, SVar (Linear t) sInfo) _ Additive{} _ = return [(name, SVar (Linear t) sInfo)]
useVar (name, SVar (Discharged t grade) sInfo) _ Additive{} Nothing = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  return [(name, SVar (Discharged t (TyGrade (Just kind) 1)) sInfo)]
useVar (name, SVar (Discharged t grade) sInfo) _ Additive{} (Just gradeOnRule) = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  return [(name, SVar (Discharged t gradeOnRule) sInfo)]

-- Defs 
-- For top level definitions we do not need to track resource usage
useVar (name, def@SDef{}) gamma Subtractive _ = return ((name, def):gamma)
useVar (name, def@SDef{}) _ Additive{} _ = return []


{--
Subtractive

------------------------ :: lin_var
Γ, x : A ⊢ A ⇒ x ; Γ

      ∃s. s + 1 = r
------------------------ :: gr_var
Γ, x : [A] r ⊢ A ⇒ x ; Γ, x : [A] s

Additive

------------------------ :: lin_var
Γ, x : A ⊢ A ⇒ x ; x : A

------------------------ :: gr_var
Γ, x : [A] r ⊢ A ⇒ x ; x : [A] 1

--}
varHelper :: (?globals :: Globals)
  => Ctxt SAssumption 
  -> FocusedCtxt SAssumption
  -> FocusedCtxt SAssumption
  -> ResourceScheme PruningScheme
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt SAssumption, Substitution, Bindings, Bool)
varHelper _ _ (Focused []) _ _ _ = none
varHelper gamma (Focused left) (Focused (var@(id, assumption) : right)) resourceScheme grade goal@(Goal (goalTySch@(Forall _ _ _ goalTy)) _) =
  varHelper gamma (Focused (var:left)) (Focused right) resourceScheme grade goal `try` do
    -- debugM "synthDebug - inside varHelper checking var: " (show var <> " against goal " <> show goalTy)
    case assumption of 
      SVar a sInfo -> do
        conv $ resetAddedConstraintsFlag -- reset the flag that says if any constraints were added
        (success, specTy, subst) <- conv $ equalTypes ns (getAssumptionType a) goalTy

        cs <- conv $ get
        -- Take the constraints generated by the type equality and add these to the synthesis predicate
        modifyPred $ addPredicateViaConjunction (Conj $ predicateStack cs) (predicateContext cs)
    
        -- Clear the checker state predicate
        conv $ modify (\s -> s { predicateStack = []}) 

        if success then do
          -- see if any constraints were added
          solved <- if addedConstraints cs
                  then solve
                  else return True
          -- now to do check we can actually use it
          if solved then do
            delta <- useVar var (gamma ++ (left ++ right)) resourceScheme grade
            return (Val ns goalTy False (Var goalTy id), delta, subst, [], isDecr sInfo)
          else none
        else none
      SDef t g -> do 
        -- Using a top level definition as a variable
        undefined





{--
Subtractive

x ∉ Δ
Γ, x : A ⊢ B ⇒ t ; Δ
------------------------ :: abs
Γ ⊢ A → B ⇒ λx . t ; Δ

Additive

Γ, x : A ⊢ B ⇒ t ; Δ, x : A
------------------------ :: abs
Γ ⊢ A → B ⇒ λx . t ; Δ

--}
absHelper :: (?globals :: Globals)
  => Ctxt SAssumption
  -> FocusedCtxt SAssumption
  -> ResourceScheme PruningScheme
  -> Bool
  -> Depth
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt SAssumption, Substitution, Bindings, Bool)
absHelper gamma (Focused omega) resourceScheme inDef depth focusPhase grade goal@(Goal goalTySch@(Forall _ binders constraints gt@(FunTy name _ tyA tyB)) sInf) = do

  -- Fresh var
  id <- useBinderNameOrFreshen name

  -- Build recursive context depending on focus mode
  let (gamma', omega') = bindToContext (id, SVar (Linear tyA) $ Just NonDecreasing) gamma omega (isLAsync tyA) 

  debugM "synthDebug" $ "(abs) lambda-binding " ++ pretty [(id, Linear tyA)]

  -- Synthesise body
  (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner resourceScheme inDef depth focusPhase gamma' (Focused omega') grade (Goal (Forall ns binders constraints tyB) sInf)

  -- Check resource use at the end
  case (resourceScheme, lookupAndCutout id delta) of
    (Additive{}, Just (delta', SVar (Linear _) _)) -> do
      return (Val ns gt False (Abs gt (PVar ns tyA False id) Nothing e), delta', subst, bindings, structurallyDecr)
    (Subtractive, Nothing) ->
      return (Val ns gt False (Abs gt (PVar ns tyA False id) Nothing e), delta, subst, bindings, structurallyDecr)
    _ -> none
absHelper _ _ _ _ _ _ _ _ = none

getSAssumptionType :: (?globals :: Globals) => SAssumption -> Synthesiser (Type, Bool, Maybe Type, Maybe StructInfo) 
getSAssumptionType (SVar (Linear t) sInfo) = return (t, False, Nothing, sInfo)
getSAssumptionType (SVar (Discharged t g) sInfo) = return (t, False, Just g, sInfo)
getSAssumptionType (SDef tySch _) = do 
  -- If this is a top level definition, we should freshen it
  (freshTy, tyVarsFreshD, substFromFreshening, constraints', _) <- conv $ freshPolymorphicInstance InstanceQ False tySch [] 
  return $ (freshTy, True, Nothing, Nothing)


appHelper :: (?globals :: Globals)
  => Ctxt SAssumption 
  -> FocusedCtxt SAssumption
  -> FocusedCtxt SAssumption 
  -> ResourceScheme PruningScheme
  -> Bool
  -> Depth
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt SAssumption, Substitution, Bindings, Bool)
appHelper _ _ (Focused []) _ _ _ _ _ _ = none
{-
Subtractive

x2 ∉ Δ1
Γ, x2 : B ⊢ C ⇒ t1 ; Δ1
Δ1 ⊢ A ⇒ t2 ; Δ2
------------------------ :: app
Γ, x1 : A → B ⊢ C ⇒ [(x1 t2) / x2] t1 ; Δ2

-}
appHelper gamma (Focused left) (Focused (var@(x, assumption) : right)) Subtractive inDef depth focusPhase grade goal@(Goal goalTySch@(Forall _ binders constraints gt) _) =
  appHelper gamma (Focused (var : left)) (Focused right) Subtractive inDef depth focusPhase grade goal `try` do
  assumptionTy <- getSAssumptionType assumption 
  (case assumptionTy of
    (FunTy _ _ tyA tyB, isTopLevelDef, _, _) -> do

      -- Only try the app if we haven't hit the app allowed depth 
      -- debugM "synthDebug - (app) trying to use a function " (show var ++ " to get goal " ++ pretty goalTySch)

      let omega = left ++ right

      leftOver <- useVar var omega Subtractive grade

      y <- freshIdentifier

      -- We need to move the assumption we have just used out of the focusing context and back into gamma
      let (gamma', omega') = 
              case lookupAndCutout x leftOver of 
                Just (omega'', var') -> (gamma ++ [(x, var')], omega'')
                _ -> (gamma, leftOver)

          -- Extend context (focused) with x2 : B
      let (gamma'', omega'') = bindToContext (y, SVar (Linear tyB) Nothing) gamma' omega' (isLAsync tyB)

      -- debugM "synthDebug - (app) try to synth the goal " (pretty goalTySch ++ "\n under context of gamma'': " ++ (show gamma'') ++ "\n , omega'': " ++ (show omega''))
      (e1, delta1, subst1, bindings1, structurallyDecr1) <- synthesiseInner Subtractive inDef depth focusPhase gamma'' (Focused omega'') grade goal
      case lookup y delta1 of
        Nothing -> do
          debugM "synthDebug - (app) try to synth the argument at type "  (pretty tyA)

          -- Synthesise the argument
          (e2, delta2, subst2, bindings2, structurallyDecr2) <- synthesiseInner Subtractive inDef depth RightSync delta1 (Focused []) grade (Goal (Forall ns binders constraints tyA) $ Just NonDecreasing)
          state <- getSynthState

          -- If this is an application of the top level def we are currently defining, then ensure the result is structurally recursive
          if not isTopLevelDef || structurallyDecr1 || structurallyDecr2 || not (x `elem` currDef state) then do
            substOut <- conv $ combineSubstitutions ns subst1 subst2
            let appExpr = App ns gt False (Val ns tyA False (Var tyA x)) e2
            return (Language.Granule.Syntax.Expr.subst appExpr y e1, delta2, substOut, bindings1 ++ bindings2, structurallyDecr1 || structurallyDecr2)
          else none
        _ -> none
    _ -> none)
{-
Additive

Γ, x2 : B ⊢ C ⇒ t1 ; Δ1, x2 : B
Γ ⊢ A ⇒ t2 ; Δ2
------------------------ :: app
Γ, x1 : A → B ⊢ C ⇒ [(x1 t2) / x2] t1 ; (Δ1 + Δ2), x1: A → B

Additive (Pruning)

Γ, x2 : B ⊢ C ⇒ t1 ; Δ1, x2 : B
Γ - Δ1 ⊢ A ⇒ t2 ; Δ2
------------------------ :: app
Γ, x1 : A → B ⊢ C ⇒ [(x1 t2) / x2] t1 ; (Δ1 + Δ2), x1: A → B

-}
appHelper gamma (Focused left) (Focused (var@(x, assumption) : right)) add@(Additive mode) inDef depth focusPhase grade goal@(Goal goalTySch@(Forall _ binders constraints gt) _) =
  appHelper gamma (Focused (var : left)) (Focused right) add inDef depth focusPhase grade goal `try` do
  assumptionTy <- getSAssumptionType assumption
  case assumptionTy of
    (FunTy _ _ tyA tyB, isTopLevelDef, _, _) -> do

      let omega = (left ++ right)
      used <- useVar var omega add grade

      y <- freshIdentifier

      -- Extend context (focused) with y : B
      let (gamma', omega') = bindToContext (y, SVar (Linear tyB) Nothing) (var:gamma) omega (isLAsync tyB)

        -- Synthesise the goal using the result of the application
      (e1, delta1, subst1, bindings1, structurallyDecr1) <- synthesiseInner add (inDef || isTopLevelDef) depth focusPhase gamma' (Focused omega') grade goal 

      -- Make sure that `y` appears in the result
      case lookupAndCutout y delta1 of
        Just (delta1',  SVar (Linear _) _) -> do
          -- Pruning subtraction
          gamma2 <-
            case mode of
              NonPruning  -> return (omega ++ (var:gamma))
              Pruning -> ctxtSubtract (omega ++ (var:gamma)) delta1'

          -- Synthesise the argument
          (e2, delta2, subst2, bindings2, structurallyDecr2) <- synthesiseInner add (inDef || isTopLevelDef) depth RightSync gamma2 (Focused []) grade (Goal (Forall ns binders constraints tyA) $ Just NonDecreasing)

          st <- getSynthState

          -- If this is an application of the top level def we are currently defining, then ensure the result is structurally recursive
          if not isTopLevelDef || structurallyDecr1 || structurallyDecr2 || not (x `elem` currDef st) then  do

            -- Add the results
            deltaOut <- maybeToSynthesiser $ ctxtAdd used delta1'
            deltaOut' <- maybeToSynthesiser $ ctxtAdd deltaOut delta2

            substOut <- conv $ combineSubstitutions nullSpan subst1 subst2
            let appExpr = App ns gt False (Val ns tyA False (Var tyA x)) e2
            return (Language.Granule.Syntax.Expr.subst appExpr y e1, deltaOut', substOut, bindings1 ++ bindings2, (structurallyDecr1 || structurallyDecr2) || isTopLevelDef)
          else none 
        _ -> none
    _ -> none


{-
Subtractive

Γ ⊢ A ⇒ t ; Δ
------------------------ :: box
Γ ⊢ [] r A ⇒ t ; Γ - r * (G - Δ)

Additive

Γ ⊢ A ⇒ t ; Δ
---------------------------- :: box
Γ ⊢ [] r A ⇒ [t] ; r * Δ

-}
boxHelper :: (?globals :: Globals)
  => Ctxt SAssumption 
  -> ResourceScheme PruningScheme
  -> Bool
  -> Depth 
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt SAssumption, Substitution, Bindings, Bool)
boxHelper gamma resourceScheme inDef depth focusPhase grade (Goal goalTySch@(Forall _ binders constraints (Box g t)) _) = 
  let newGradeOnRule = case grade of Just gradeOnRule -> Just $ TyInfix TyOpTimes gradeOnRule g ; Nothing -> Nothing
  in case resourceScheme of
      Additive{} -> do
        (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner resourceScheme inDef depth focusPhase gamma (Focused []) newGradeOnRule (Goal (Forall ns binders constraints t) $ Just NonDecreasing) 
        case hasLinear delta of 
          False -> do deltaOut <- 
                        case newGradeOnRule of 
                          Just _ -> return delta
                          Nothing -> ctxtMultByCoeffect g delta
                      let boxExpr = Val ns t False (Promote t e)
                      return (boxExpr, deltaOut, subst, bindings, structurallyDecr)
          True  -> none
      Subtractive -> do
        (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner resourceScheme inDef depth focusPhase gamma (Focused []) newGradeOnRule (Goal (Forall ns binders constraints t) $ Just NonDecreasing)
        deltaOut <- case newGradeOnRule of
            Just _ -> return delta
            Nothing -> do
              used <- ctxtSubtract gamma delta
              -- Compute what was used to synth e
              delta' <- ctxtMultByCoeffect g used
              ctxtSubtract gamma delta'
        res <- solve
        let boxExpr = Val ns t False (Promote t e)
        boolToSynthesiser res (boxExpr, deltaOut, subst, bindings, structurallyDecr)
  
  where 

    hasLinear [] = False
    hasLinear ((x, SVar (Linear _) _):xs) = True
    hasLinear ((x, _):xs) = hasLinear xs

boxHelper _ _ _ _ _ _ _ = none


unboxHelper :: (?globals :: Globals)
  => Ctxt SAssumption
  -> FocusedCtxt SAssumption 
  -> FocusedCtxt SAssumption
  -> ResourceScheme PruningScheme
  -> Bool
  -> Depth  
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt SAssumption, Substitution, Bindings, Bool)
unboxHelper _ _ (Focused []) _ _ _ _ _ _ = none
{-
Subtractive
0 <= s
Γ, x2 : [A] r ⊢ B ⇒ e ; Δ, x2 : [A] s
-------------------------------------------- :: unbox
Γ, x1 : [] r A ⊢ B ⇒ let [x2] = x1 in e; Δ

-}
unboxHelper gamma (Focused left) (Focused (var@(x, assumption) : right)) Subtractive inDef depth focusPhase grade goal@(Goal goalTySch _) =
  unboxHelper gamma (Focused (var : left)) (Focused right) Subtractive inDef depth focusPhase grade goal `try` do
    assumptionTy <- getSAssumptionType assumption
    case assumptionTy of
      ((Box grade_r tyA), False, Nothing, sInfo) -> do

        -- debugM "synthDebug" $ "Trying to unbox " ++ show assumption

        let omega = left ++ right
        leftOver <- useVar var omega Subtractive grade
        y <- freshIdentifier
        let (gamma', omega') = bindToContext (y, SVar (Discharged tyA grade_r) sInfo) gamma leftOver (isLAsync tyA)
        -- debugM "synthDebug" $ "Inside unboxing try to synth for " ++ pretty goalTySch ++ " under " ++ pretty [(y, Discharged tyA grade_r)]

        (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner Subtractive inDef depth focusPhase gamma' (Focused omega') grade goal
        case lookupAndCutout y delta of
          Just (delta', SVar (Discharged _ grade_s) _) -> do
            -- Check that: 0 <= s
            (kind, _, _) <- conv $ synthKind nullSpan grade_s
            s <- conv get
            modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyGrade (Just kind) 0) grade_s kind) (predicateContext s)
            res <- solve

            -- If we succeed, create the let binding
            boolToSynthesiser res (makeUnbox y x goalTySch (Box grade_r tyA) tyA e, delta', subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr)
          _ -> none
      ((Box grade_r tyA), False, Just grade_s, Just sInfo) -> do
        debugM "synthDebug - (unbox - double) trying a double unboxing with "  (show grade_r)
      
        let omega = left ++ right
        leftOver <- useVar var [] Subtractive grade 
        y <- freshIdentifier
        let (gamma', omega') = bindToContext (y, SVar (Discharged tyA (TyInfix TyOpTimes grade_r grade_s)) $ Just sInfo) gamma omega (isLAsync tyA) 
        (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner Subtractive inDef depth focusPhase gamma' (Focused omega') grade goal 
        case lookupAndCutout y delta of
          Just (delta', SVar (Discharged _ grade_s') _) ->  do 
            (kind, _, _) <- conv $ synthKind nullSpan grade_s'
            r' <- freshIdentifier 
            conv $ existentialTopLevel r' kind
            s <- conv get
            modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyInfix TyOpTimes (TyVar r') grade_s) grade_s' kind) (predicateContext s)
            res <- solve 
            debugM "synthDebug - (unbox - double) term: " (pretty $ makeUnbox y x goalTySch (Box grade_r tyA) tyA e)
            boolToSynthesiser res (makeUnbox y x goalTySch (Box grade_r tyA) tyA e, replace delta' x (SVar (Discharged (Box grade_r tyA) (TyVar r')) $ Just sInfo), subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr)
          _ -> none
      _ -> none
{-
Additive

s <= r
Γ, x2 : [A] r ⊢ B ⇒ t ; D, x2 : [A] s
--------------------------------------------------------- :: unbox
Γ, x1 : [] r A ⊢ B ⇒ let [x2] = x1 in t ; Δ, x1 : [] r A

-}
unboxHelper gamma (Focused left) (Focused (var@(x, ty) : right)) add@(Additive{}) inDef depth focusPhase grade goal@(Goal goalTySch _) =
  unboxHelper gamma (Focused (var : left)) (Focused right) add inDef depth focusPhase grade goal `try`
  case ty of
    (SVar (Linear (Box grade_r tyA)) sInfo) -> do
      let omega = left ++ right
      used <- useVar var omega add grade
      y <- freshIdentifier

      let (gamma', omega') = bindToContext (y, SVar (Discharged tyA grade_r) sInfo) gamma omega (isLAsync tyA)

      -- Synthesise the body of a `let` unboxing
      (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner add inDef depth focusPhase gamma' (Focused omega') grade goal

      -- Add usage at the binder to the usage in the body
      delta' <- maybeToSynthesiser $ ctxtAdd used delta

      s <- conv get

      case lookupAndCutout y delta' of
        Just (delta'', SVar (Discharged _ grade_s) _) -> do
          (kind, _, _) <- conv $ synthKind nullSpan grade_r
          modifyPred $ addConstraintViaConjunction (ApproximatedBy ns grade_s grade_r kind) (predicateContext s)
          res <- solve
          boolToSynthesiser res (makeUnbox y x goalTySch tyA (Box grade_r tyA) e,  delta'', subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr) 
        _ -> do
          (kind, _, _) <- conv $ synthKind nullSpan grade_r
          modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyGrade (Just kind) 0) grade_r kind) (predicateContext s)
          res <- solve
          boolToSynthesiser res (makeUnbox y x goalTySch tyA (Box grade_r tyA) e,  delta', subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr) 
    (SVar (Discharged (Box grade_r tyA) grade_s) sInfo) -> do
      let omega = left ++ right
      used <- useVar var [] add grade
      y <- freshIdentifier
      let (gamma', omega') = bindToContext (y, SVar (Discharged tyA (TyInfix TyOpTimes grade_r grade_s)) sInfo) gamma omega (isLAsync tyA)
      (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner add inDef depth focusPhase gamma' (Focused omega') grade goal 

      s <- conv get

      case lookupAndCutout y delta of
        Just (delta', SVar (Discharged _ grade_s') _) ->  do
          (kind, _, _) <- conv $ synthKind nullSpan grade_s'
          r' <- freshIdentifier 
          conv $ existentialTopLevel r' kind

          modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyInfix TyOpTimes (TyVar r') grade_s) (TyInfix TyOpTimes grade_r grade_s) kind) (predicateContext s)
          modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyInfix TyOpTimes (TyVar r') grade_s) grade_s' kind) (predicateContext s)

          res <- solve

          boolToSynthesiser res (makeUnbox y x goalTySch (Box grade_r tyA) tyA e, replace delta x (SVar (Discharged (Box grade_r tyA) (TyVar r')) sInfo), subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr)
        _ -> do
            (kind, _, _) <- conv $ synthKind nullSpan grade_r
            modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyGrade (Just kind) 0) (TyInfix TyOpTimes grade_r grade_s) kind) (predicateContext s)
            res <- solve
            boolToSynthesiser res (makeUnbox y x goalTySch (Box grade_r tyA) tyA e, delta, subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr)
    _ -> none



{-- 


--}
constrIntroHelper :: (?globals :: Globals)
  => Ctxt SAssumption
  -> ResourceScheme PruningScheme
  -> Bool
  -> Depth 
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt SAssumption, Substitution, Bindings, Bool)
constrIntroHelper gamma resourceScheme False depth focusPhase grade goal@(Goal goalTySch@(Forall s binders constraints tyA) sInfo) =
  case (isADTorGADT tyA) of
    Just name -> do
      if iCurrent depth <= intros depth || isDecr sInfo then do

        state <- getSynthState
        let (recursiveCons, nonRecursiveCons) = relevantConstructors name (constructors state)
        let sortedCons = sortBy compareArity nonRecursiveCons ++ sortBy compareArity recursiveCons

        -- For each relevent data constructor, we must now check that it's type matches the goal
        (maybeExpr, deltaOut, substOut, bindingsOut, structurallyDecrOut) <- tryConstructors name state [] sortedCons
        case maybeExpr of  
          Just expr -> return (expr, deltaOut, substOut, bindingsOut, False)
          _ -> none
      else none
    _ -> none
  where

    tryConstructors _ _ _ [] = none
    tryConstructors adtName state right ((conName, (conTySch@(Forall s conBinders conConstraints conTy), conSubst)):left) = 
      tryConstructors adtName state ((conName, (conTySch, conSubst)):right) left `try` do
        result <- checkConstructor False conTySch tyA conSubst
        case result of 
          (True, specTy, _, specSubst, substFromFreshening) -> do
            specTy' <- conv $ substitute substFromFreshening specTy
            subst' <- conv $ combineSubstitutions s conSubst specSubst
            specTy'' <- conv $ substitute subst' specTy'
            debugM "synthDebug - constrIntroHelper - synthing arguments for: " (show conName)
            case constrArgs conTy of 
              Just [] -> do 
                let delta = case resourceScheme of Additive{} -> [] ; Subtractive{} -> gamma

                let conExpr = Val ns (TyCon conName) True (Constr (TyCon conName) conName [])
                return (Just $ conExpr, delta, conSubst, [], False) 
              Just conArgs -> do 
                args <- conv $ mapM (\s -> do 
                  s' <- substitute substFromFreshening s
                  s'' <- substitute specSubst s'
                  return (s'', Just $ boolToStructure $ isDecreasing adtName [s])) conArgs
                (exprs, delta, subst, bindings, structurallyDecr) <- synthConArgs adtName (constructors state) args conBinders conConstraints conSubst
                return (Just $ makeConstr exprs conName conTy, delta, subst, bindings, structurallyDecr) 
              Nothing -> none
          _ -> none

    constrArgs :: Type -> Maybe [Type]
    constrArgs (TyCon _) = Just []
    constrArgs (TyApp _ _) = Just []
    constrArgs (FunTy _ _ e1 e2) = do
      res <- constrArgs e2
      return $ e1 : res
    constrArgs _ = Nothing

    -- Traverse the argument types to the constructor and synthesise a term for each one
    synthConArgs tyAName consGlobal [(argTyA, sInfo)] conBinders conConstraints conSubst = do
      let newDepth = if isDecr sInfo then depth { iCurrent = (iCurrent depth) + 1 } else depth
      (expr, delta, subst, bindings, structurallyDecr) <- synthesiseInner resourceScheme False newDepth RightAsync gamma (Focused []) grade (Goal (Forall s conBinders conConstraints argTyA) sInfo)
      subst' <- conv $ combineSubstitutions ns conSubst subst
      return ([(expr, argTyA)], delta, subst', bindings, structurallyDecr)
    synthConArgs tyAName consGlobal ((argTyA, sInfo):args) conBinders conConstraints conSubst = do
      (exprs, deltas, substs, bindings, structurallyDecr) <- synthConArgs tyAName consGlobal args conBinders conConstraints conSubst
      substs' <- conv $ combineSubstitutions ns conSubst substs
      gamma' <- case resourceScheme of
            Additive NonPruning -> return gamma
            Additive Pruning -> ctxtSubtract gamma deltas -- Pruning
            Subtractive -> return deltas
      let newDepth = if isDecr sInfo then depth { iCurrent = (iCurrent depth) + 1 } else depth
      (expr, delta, subst, bindings', structurallyDecr') <- synthesiseInner resourceScheme False newDepth RightAsync gamma' (Focused []) grade (Goal (Forall s conBinders conConstraints argTyA) sInfo)
      subst'' <- conv $ combineSubstitutions ns subst substs'
      delta' <- case resourceScheme of
            Additive{} -> maybeToSynthesiser $ ctxtAdd deltas delta
            Subtractive -> return delta
      return ((expr, argTyA):exprs, delta', subst'', bindings ++ bindings', structurallyDecr || structurallyDecr')
    synthConArgs _ _ _ _ _ _ = none

    boolToStructure False = NonDecreasing
    boolToStructure True  = Decreasing 0

constrIntroHelper _ _ _ _ _ _ _ = none





{- 

Constructor elimination synthesis
---------------------------------


-}
constrElimHelper :: (?globals :: Globals)
  => Ctxt SAssumption
  -> FocusedCtxt SAssumption
  -> FocusedCtxt SAssumption
  -> ResourceScheme PruningScheme
  -> Bool 
  -> Depth
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt SAssumption, Substitution, Bindings, Bool)
constrElimHelper _ _ (Focused []) _ _ _ _ _ _ = none
constrElimHelper gamma (Focused left) (Focused (var@(x, assumption):right)) mode False depth focusPhase grade goal@(Goal goalTySch@(Forall _ _ _ tyB) _) =
  constrElimHelper gamma (Focused (var:left)) (Focused right) mode False depth focusPhase grade goal `try` do
    assumptionTy <- getSAssumptionType assumption 
    case assumptionTy of 
      (tyA', False, assumptionGrade, Just sInfo) -> do   
        let (allowElim, currentDepth) = case sInfo of 
              Decreasing eDepth -> (eDepth <= elims depth, eDepth)
              _ -> (True, 0)
        if allowElim then do
          -- debugM "synthDebug in constrElimHelper with assumption: " (show assumption <> " and goal " <> show tyB)
          case isADTorGADT tyA' of
            Just name -> do
              let omega = (left ++ right)
              usageOut <- useVar var omega mode grade
              state <- getSynthState
       
              let (recursiveCons, nonRecursiveCons) = relevantConstructors name (constructors state)
              let sortedCons = sortBy compareArity nonRecursiveCons ++ sortBy compareArity recursiveCons

              (patterns, delta, resSubst, resBindings, structurallyDecr, _) <- foldM (\ (exprs, deltas, substs, bindings, structurallyDecr, index) (conId, (conTySch@(Forall s binders constraints conTy), conSubst)) -> do

                cs <- conv get
                let pred = newImplication [] (predicateContext cs)

                debugM "compiletoSBV ELIM (check constructor)" $ pretty conId
                result <- checkConstructor True conTySch tyA' conSubst

                let predSucceeded = moveToConsequent pred

                case (result, predSucceeded) of 
                  ((True, specTy, conTyArgs, conSubst', _), Right pred'@(ImplConsequent ctxt p path)) -> do

                    modifyPred pred'

                    -- Calculate assumptions
                    assumptions <- mapM (\ (arg, _) -> do
                      y <- freshIdentifier 
                      arg' <- conv $ substitute conSubst' arg
                      let assumptionType = case assumptionGrade of {Nothing -> Linear arg'; Just grade_r -> Discharged arg' grade_r}
                      let assumption = if isRecursiveCon name (y, (Forall ns binders constraints arg, [])) 
                          then (y, (SVar assumptionType $ Just (Decreasing $ currentDepth+1))) 
                          else (y, (SVar assumptionType $ Just NonDecreasing ))
                      return assumption) conTyArgs
                  
                    let (vars, _) = unzip assumptions
                    let constrElimPattern = makePattern conId vars grade


                    -- If we are rebinding the assumption we are currently doing the eliminatino on (i.e. if it's graded) then
                    -- we need to rebing it in gamma NOT omega. Otherwise we will end up staying focused on it and trying to use
                    -- it even when we can not 

                    (gamma', omega') <- 
                      case mode of 
                        Additive{} -> return (gamma, omega) --return (((x, (tyA, (AInfo structure (eDepth+1)))):gamma), omega)
                        Subtractive -> 
                          case lookupAndCutout x usageOut of 
                            Just (usageOut', assumption') -> return (gamma ++ [(x, assumption')], usageOut')
                            _ -> return (gamma, usageOut)                  
                  
                    -- Required for focusing with recursive data structures. If we have hit the depth limit but still have other vars in omega 
                    -- that cannot be decomposed we need to move them into gamma

                    let reachedDepth = currentDepth + 1 > elims depth

                    let (gamma'', omega'', unboxed) = bindAssumptions reachedDepth [] assumptions gamma' omega'

                    (expr, delta, subst, bindings, structurallyDecr') <- synthesiseInner mode False depth focusPhase gamma'' (Focused omega'') grade goal 
                
                    delta' <- checkAssumptions (x, tyA') mode delta assumptions unboxed
                  
                    case transformPattern bindings tyA' (gamma'' ++ omega'') constrElimPattern unboxed of
                      Just (pattern, bindings') ->
                        let mergeOp = case mode of Additive{} -> TyInfix TyOpJoin ; _ -> TyInfix TyOpMeet in do
                          returnDelta <- if index == 0 then return delta' else ctxtMerge mergeOp deltas delta' 
                          modifyPred $ moveToNewConjunct (predicateContext cs)
                          returnSubst <- conv $ combineSubstitutions ns subst substs
                          return ((pattern, expr):exprs, returnDelta, returnSubst, bindings ++ bindings', structurallyDecr || structurallyDecr', index + 1)
                      Nothing -> do 
                        modifyPred $ moveToNewConjunct (predicateContext cs)
                        return (exprs, deltas, substs, bindings, structurallyDecr, index)
                  _ -> do 
                    modifyPred $ moveToNewConjunct (predicateContext cs)
                    return (exprs, deltas, substs, bindings, structurallyDecr, index)
                ) ([], [], [], [], False, 0) sortedCons
              case patterns of 
                (_:_) -> do 
                  finDelta <- case (mode, assumptionGrade) of {(Additive{}, Nothing) -> maybeToSynthesiser $ ctxtAdd usageOut delta; _ -> return delta}
                  return (makeCase tyA' x patterns tyB assumptionGrade, finDelta, resSubst, resBindings, structurallyDecr)
                _ -> none
            _ -> none   
        else none
      _ -> none

  where 

  makePattern :: Id -> [Id] -> Maybe Type -> Pattern ()
  makePattern conId vars _ = PConstr ns () False conId (map (PVar ns () False) vars)
    
  bindAssumptions :: 
    Bool
    -> Ctxt SAssumption 
    -> Ctxt SAssumption
    -> Ctxt SAssumption
    -> Ctxt SAssumption
    -> (Ctxt SAssumption, Ctxt SAssumption, Ctxt SAssumption)
  bindAssumptions depthReached unboxed [] gamma omega = (gamma, omega, unboxed)

  bindAssumptions depthReached unboxed (assumption@(id, SVar (Linear t) sInfo):assmps) gamma omega =
    let gammaOrOmega = if depthReached && isDecr sInfo then False else isLAsync t in
    let (gamma', omega') = bindToContext assumption gamma omega gammaOrOmega in
    bindAssumptions depthReached unboxed assmps gamma' omega' 

  bindAssumptions depthReached unboxed (assumption@(id, SVar (Discharged (Box t grade) grade') sInfo):assmps) gamma omega =
    let gammaOrOmega = if depthReached && isDecr sInfo then False else isLAsync t in
    let (gamma', omega') = bindToContext (id, SVar (Discharged t (TyInfix TyOpTimes grade grade')) sInfo) gamma omega gammaOrOmega in
    bindAssumptions depthReached ((id, SVar (Discharged t (TyInfix TyOpTimes grade grade')) sInfo):unboxed) assmps gamma' omega' 

  bindAssumptions depthReached unboxed (assumption@(id, SVar (Discharged t _) sInfo):assmps) gamma omega =
    let gammaOrOmega = if depthReached && isDecr sInfo then False else isLAsync t in
    let (gamma', omega') = bindToContext assumption gamma omega gammaOrOmega in
    bindAssumptions depthReached unboxed assmps gamma' omega' 
  
  bindAssumptions depthReached unboxed ((id, _):assmps) gamma omega = (gamma, omega, unboxed)


  
  -- Checks that assumptions bound via constrElim were used correctly in the synthesised term
  checkAssumptions :: (?globals::Globals) 
    => (Id, Type)
    -> ResourceScheme PruningScheme
    -> Ctxt SAssumption
    -> Ctxt SAssumption
    -> Ctxt SAssumption 
    -> Synthesiser (Ctxt SAssumption)
  checkAssumptions _ mode del [] _ = return del
  checkAssumptions x sub@Subtractive{} del ((id, SVar (Linear t) _):assmps) unboxed =
    case lookup id del of
      Nothing -> checkAssumptions x sub del assmps unboxed
      _ -> none
  checkAssumptions (x, t') sub@Subtractive{} del ((id, (SVar (Discharged t g) info)):assmps) unboxed = do
    s <- conv get
    case lookupAndCutout id del of
      Just (del', (SVar (Discharged _ g') sInfo)) ->
        case lookup id unboxed of
          Just (SVar (Discharged _ g'') sInfo') -> do
            del'' <- checkAssumptions (x, t') sub del' assmps unboxed
            (kind, _, _) <- conv $ synthKind nullSpan g'
            modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyGrade (Just kind) 0) g' kind) (predicateContext s)
            res <- solve
            if res then do
              ctxtMerge (TyInfix TyOpMeet) [(x, (SVar (Discharged t' g) sInfo))] del''
            else none
          _ -> do
            del'' <- checkAssumptions (x, t') sub del' assmps unboxed
            (kind, _, _) <- conv $ synthKind nullSpan g'
            modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyGrade (Just kind) 0) g' kind) (predicateContext s)
            res <- solve
            if res then
              ctxtMerge (TyInfix TyOpMeet) [(x, (SVar (Discharged t' g') sInfo))] del''
            else none
      _ -> none

  -- Additive
  checkAssumptions x add@Additive{} del ((id, SVar (Linear t) sInfo):assmps) unboxed =
    case lookupAndCutout id del of
      Just (del', _) ->
        checkAssumptions x add del' assmps unboxed
      _ -> none
  checkAssumptions (x, t') add@Additive{} del ((id, SVar (Discharged t g) sInfo):assmps) unboxed = do
        s <- conv get
        case lookupAndCutout id del of
          Just (del', (SVar (Discharged _ g') sInfo')) ->
            case lookup id unboxed of
              Just (SVar (Discharged _ g'') sInfo'') -> do
                del'' <- checkAssumptions (x, t') add del' assmps unboxed
                (kind, _, _) <- conv $ synthKind nullSpan g'
                modifyPred $ addConstraintViaConjunction (ApproximatedBy ns g' g'' kind) (predicateContext s)
                res <- solve
                if res then 
                  ctxtMerge (TyInfix TyOpJoin) [(x, SVar (Discharged t' g) sInfo)] del''
                else none
              _ -> do
                del'' <- checkAssumptions (x, t') add del' assmps unboxed
                (kind, _, _) <- conv $ synthKind nullSpan g
                modifyPred $ addConstraintViaConjunction (ApproximatedBy ns g' g kind) (predicateContext s)
                res <- solve
                if res then 
                  ctxtMerge (TyInfix TyOpJoin) [(x, SVar (Discharged t' g') sInfo)] del''
                else none
          _ -> do
            (kind, _, _) <- conv $ synthKind nullSpan g
            modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyGrade (Just kind) 0) g kind) (predicateContext s)
            res <- solve
            if res then checkAssumptions (x, t') add del assmps unboxed else none
          
  -- Top level definitions should never appear in delta, however, just skip over them if so 
  checkAssumptions x mode del (var@(id, SDef{}):assmps) unboxed = checkAssumptions x mode del assmps unboxed 


  -- Construct a typed pattern from an untyped one from the context
  transformPattern :: 
       Ctxt (Id, Type)
    -> Type 
    -> Ctxt SAssumption 
    -> Pattern () 
    -> Ctxt SAssumption 
    -> Maybe (Pattern Type, Ctxt (Id, Type))
  transformPattern bindings adt ctxt (PConstr s () b id pats) unboxed = do
    (pats', bindings') <- transformPatterns bindings adt ctxt pats unboxed
    Just (PConstr s adt b id pats', bindings)
  transformPattern bindings adt ctxt (PVar s () b name) unboxed =
    let (pat, name', bindings') = case lookup name unboxed of
          Just (SVar (Discharged ty _) _) -> (PBox s ty False, name, bindings)
          _ -> (id, name, bindings)
    in
    case lookup name ctxt of
       Just (SVar (Linear t) _) -> Just (pat $ PVar s t b name', bindings')
       Just (SVar (Discharged t c) _) -> Just (pat $ PVar s t b name', bindings')
       _ -> Nothing
  transformPattern bindings adt ctxt (PBox s () b p) unboxed = do
    (pat', bindings') <- transformPattern bindings adt ctxt p unboxed
    Just (PBox s adt b pat', bindings')
  transformPattern _ _ _ _ _ = Nothing


  transformPatterns :: 
       Ctxt (Id, Type) 
    -> Type 
    -> Ctxt SAssumption 
    -> [Pattern ()]
    -> Ctxt SAssumption
    -> Maybe ([Pattern Type], Ctxt (Id, Type))
  transformPatterns bindings adt ctxt [] unboxed = Just ([], bindings)
  transformPatterns bindings adt ctxt (p:ps) unboxed = do
    (pat, bindings') <- transformPattern bindings adt ctxt p unboxed
    (res, bindingsFinal) <- transformPatterns bindings' adt ctxt ps unboxed
    return (pat:res, bindingsFinal)

constrElimHelper _ _ _ _ _ _ _ _ _ = none



synthesiseInner :: (?globals :: Globals)
           => ResourceScheme PruningScheme       
           -> Bool
           -> Depth 
           -> FocusPhase     
           -> Ctxt SAssumption    -- (unfocused) free variables
           -> FocusedCtxt SAssumption    -- focused variables
           -> Maybe Type
           -> Goal          
           -> Synthesiser (Expr () Type, Ctxt SAssumption, Substitution, Bindings, Bool)
synthesiseInner resourceScheme inDef depth focusPhase gamma (Focused omega) grade goal@(Goal goalTySch@(Forall _ _ _ ty) info) = do

  currentTime    <- liftIO $ Clock.getTime Clock.Monotonic

  Synthesiser $ lift $ lift $ lift $ modify (\state ->
            state {
                depthReached = if not $ depthReached state then iCurrent depth >= intros depth else True
                  })

  case (focusPhase, omega) of 
    (RightAsync, _) -> do
      varHelper [] (Focused []) (Focused (gamma ++ omega)) resourceScheme grade goal
      `try`
      absHelper gamma (Focused omega) resourceScheme inDef depth RightAsync grade goal
      `try`
      rightAsyncTrans ty
    (LeftAsync, (_:_)) -> do 
      varHelper [] (Focused []) (Focused (gamma ++ omega)) resourceScheme grade goal
      `try`
      unboxHelper gamma (Focused []) (Focused omega) resourceScheme inDef depth LeftAsync grade goal
      `try`
      constrElimHelper gamma (Focused []) (Focused omega) resourceScheme inDef depth LeftAsync grade goal
    (LeftAsync, []) -> do
      focus gamma (isRSync ty) 
    (RightSync, []) ->
      case not $ isRSync ty of 
        True -> 
          synthesiseInner resourceScheme inDef depth RightAsync gamma (Focused []) grade goal
        _ -> 
          varHelper [] (Focused []) (Focused gamma) resourceScheme grade goal
          `try`
          constrIntroHelper gamma resourceScheme inDef depth RightSync grade goal
          `try`
          boxHelper gamma resourceScheme inDef depth RightSync grade goal
    (LeftSync, var@(x, assumption):[]) -> do
      assumptionTy <- getSAssumptionType assumption 
      case assumptionTy of 
        (tyA', _, _, _) -> 
          case (not $ isLSync tyA') && (not $ isAtomic tyA') of 
            True -> synthesiseInner resourceScheme inDef depth LeftAsync gamma (Focused [var]) grade goal
            _ -> do
              varHelper gamma (Focused []) (Focused omega) resourceScheme grade goal
              `try`
              appHelper gamma (Focused []) (Focused omega) resourceScheme inDef depth LeftSync grade goal
    (LeftSync, []) -> do
        synthesiseInner resourceScheme inDef depth RightAsync gamma (Focused []) grade goal

  where 

    rightAsyncTrans (FunTy{}) = none 
    rightAsyncTrans _ = synthesiseInner resourceScheme inDef depth LeftAsync gamma (Focused omega) grade goal

    focus gamma True =  
      synthesiseInner resourceScheme inDef depth RightSync gamma (Focused []) grade goal
      `try`
      focusLeft [] gamma 
    focus gamma False = focusLeft [] gamma

    focusLeft _ [] = none
    focusLeft left (var:right) = 
      focusLeft (var : left) right
      `try`
      synthesiseInner resourceScheme inDef depth LeftSync (left ++ right) (Focused [var]) grade goal
    



synthesise :: (?globals :: Globals) 
           => ResourceScheme PruningScheme    -- whether the synthesis is in additive mode or not
           -> Ctxt SAssumption    -- (unfocused) free variables
           -> FocusedCtxt SAssumption    -- focused variables
           -> Depth 
           -> Maybe Type
           -> Goal           -- type from which to synthesise
           -> Synthesiser (Expr () Type, Ctxt SAssumption, Substitution)
synthesise resourceScheme gamma (Focused omega) depth grade goal = do

  st' <- get
  relevantConstructors <- do 
      let snd3 (a, b, c) = b
      st <- get
      let pats = map (second snd3) (typeConstructors st)
      mapM (\ (a, b) -> do
          dc <- conv $ mapM (lookupDataConstructor ns) b
          let sd = zip (fromJust $ lookup a pats) (catMaybes dc)
          return (a, sd)) pats

  relevantConstructorsWithRecLabels <- mapM (\(tyId, dataCons) -> 
                          do 
                            hasRecCon <- foldM (\a (dataConName, (Forall _ _ _ dataTy, _)) -> 
                              case a of 
                                True -> return True
                                _ -> return $ markRecursiveType tyId dataTy 
                              ) False dataCons
                            return (tyId, (dataCons, hasRecCon))) relevantConstructors

  Synthesiser $ lift $ lift $ lift $ modify (\state ->
            state {
             constructors = relevantConstructorsWithRecLabels
                  })

  result@(expr, ctxt, subst, bindings, _) <- synthesiseInner resourceScheme False depth RightAsync gamma (Focused omega) grade goal

  case resourceScheme of
    Subtractive -> do
      -- All linear variables should be gone
      -- and all graded should approximate 0
      consumed <- mapM (\(id, a) ->
                    case a of
                      (SVar Linear{} _) -> return False;
                      (SVar (Discharged _ grade) _) -> do
                        (kind, _, _) <-  conv $ synthKind nullSpan grade
                        s <- conv get 
                        modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyGrade (Just kind) 0) grade kind) (predicateContext s)
                        solve
                      _ -> return True) ctxt
      if and consumed
        then return (expr, ctxt, subst)
        else none

    -- All linear variables should have been used
    -- and all graded assumptions should have usages which approximate their original assumption
    Additive{} -> do
      consumed <- mapM (\(id, a) ->
                    case lookup id ctxt of
                      Just (SVar Linear{} _) -> return True;
                      Just (SVar (Discharged _ gradeUsed) _) ->
                        case a of
                          (SVar (Discharged _ gradeSpec) _) -> do
                            (kind, _, _) <- conv $ synthKind nullSpan gradeUsed
                            s <- conv get
                            modifyPred $ addConstraintViaConjunction (ApproximatedBy ns gradeUsed gradeSpec kind) (predicateContext s)
                            solve
                          (SVar (Linear _) _) -> return False
                          _ -> return True
                      Just (SDef{}) -> return True
                      Nothing ->
                        case a of
                          (SVar (Discharged _ gradeSpec) _) -> do
                            (kind, _, _) <- conv $ synthKind nullSpan gradeSpec
                            s <- conv get
                            modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (TyGrade (Just kind) 0) gradeSpec kind) (predicateContext s)
                            solve
                          (SVar (Linear _) _) -> return False
                          _ -> return True) (gamma ++ omega)
      if and consumed
        then return (expr, ctxt, subst)
        else none


-- Run from the checker
synthesiseProgram :: (?globals :: Globals)
           => Maybe Hints
           -> Int -- index
           -> Ctxt TypeScheme  -- Unrestricted Defs 
           -> Ctxt (TypeScheme, Type) -- Restricted Defs
           -> Id
           -> Ctxt Assumption    -- (unfocused) free variables
           -> TypeScheme           -- type from which to synthesise
           -> CheckerState
           -> IO [Expr () ()]
synthesiseProgram hints index unrComps rComps defId ctxt goalTy checkerState = do

  start <- liftIO $ Clock.getTime Clock.Monotonic

  let (timeoutLim, index, gradeOnRule, resourceScheme) =
         case hints of 
            Just hints' -> ( case (hTimeout hints', hNoTimeout hints') of 
                                  (_, True) -> -1
                                  (Just lim, _) -> lim * 1000,
                            index + (fromMaybe 0 $ hIndex hints'),
                            hGradeOnRule hints' || fromMaybe False (globalsGradeOnRule ?globals),
                            let mode = if (hPruning hints' || alternateSynthesisMode) then Pruning else NonPruning
                            in 
                            if (hSubtractive hints' || subtractiveSynthesisMode) then Subtractive else Additive mode 
                          )
            Nothing ->    ( -1,
                            index, 
                            fromMaybe False (globalsGradeOnRule ?globals), 
                            let mode = if alternateSynthesisMode then Pruning else NonPruning
                            in 
                            if subtractiveSynthesisMode then Subtractive else Additive mode)

  let gamma = map (\(v, a)  -> (v, (SVar a $ Just NonDecreasing))) ctxt ++ 
              map (\(v, (Forall _ _ _ ty, grade)) -> (v, (SVar (Discharged ty grade) $ Just NonDecreasing))) rComps
  let initialGrade = if gradeOnRule then Just (TyGrade Nothing 1)  else Nothing

  let initialState = SynthesisData {
                         smtCallsCount= 0 
                      ,  smtTime= 0 
                      ,  proverTime= 0 
                      ,  theoremSizeTotal= 0 
                      ,  pathsExplored= 0 
                      ,  startTime=start 
                      ,  constructors=[] 
                      ,  currDef = [defId]
                      ,  depthReached = False
                      }

  let (hintELim, hintILim) = (1, 1) -- case (hasElimHint hints, hasIntroHint hints) of 
  --           (Just e, Just i)   -> (e, i)
  --           (Just e, Nothing)  -> (e, 1)
  --           (Nothing, Just i)  -> (1, i)
  --           (Nothing, Nothing) -> (1, 1)

  result <- liftIO $ System.Timeout.timeout timeoutLim $ loop resourceScheme (hintELim, hintILim) index unrComps initialGrade gamma initialState
  fin <- case result of 
    Just (synthResults, aggregate) ->  do
      let results = nub $ map fst3 $ rights (map fst synthResults)

      -- Force eval of first result (if it exists) to avoid any laziness when benchmarking
      () <- when benchmarking $ unless (null results) (return $ seq (show $ head results) ())
  -- %%
      end    <- liftIO $ Clock.getTime Clock.Monotonic

      debugM "mode used: " (show resourceScheme)
      debugM "results: " (pretty results)
      case results of
      -- Nothing synthed, so create a blank hole instead
        []    -> do
          debugM "Synthesiser" $ "No programs synthesised for " <> pretty goalTy
          printInfo $ "No programs synthesised" 
        _ ->
          case last results of
            t -> do
              debugM "Synthesiser" $ "Synthesised: " <> pretty t
              printSuccess "Synthesised"

      -- <benchmarking-output>
      when benchmarking $
        if benchmarkingRawData then
          putStrLn $ "Measurement "
            <> "{ smtCalls = " <> show (smtCallsCount aggregate)
            <> ", synthTime = " <> show (fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double))
            <> ", proverTime = " <> show (proverTime aggregate)
            <> ", solverTime = " <> show (Language.Granule.Synthesis.Monad.smtTime aggregate)
            <> ", meanTheoremSize = " <> show (if smtCallsCount aggregate == 0 then 0 else fromInteger (theoremSizeTotal aggregate) / fromInteger (smtCallsCount aggregate))
            <> ", success = " <> (if null results then "False" else "True")
            <> ", timeout = False"
            <> ", pathsExplored = " <> show (pathsExplored aggregate)
            <> " } "
        else do
          -- Output benchmarking info
          putStrLn "-------------------------------------------------"
          putStrLn $ "Result = " ++ (case synthResults of ((Right (expr, _, _), _):_) -> pretty expr; _ -> "NO SYNTHESIS")
          putStrLn $ "-------- Synthesiser benchmarking data (" ++ show resourceScheme ++ ") -------"
          putStrLn $ "Total smtCalls     = " ++ show (smtCallsCount aggregate)
          putStrLn $ "Total smtTime    (ms) = "  ++ show (Language.Granule.Synthesis.Monad.smtTime aggregate)
          putStrLn $ "Total proverTime (ms) = "  ++ show (proverTime aggregate)
          putStrLn $ "Total synth time (ms) = "  ++ show (fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double))
          putStrLn $ "Mean theoremSize   = " ++ show ((if smtCallsCount aggregate == 0 then 0 else fromInteger $ theoremSizeTotal aggregate) / fromInteger (smtCallsCount aggregate))
      -- </benchmarking-output>
      return (map unannotateExpr results)
    _ -> do
      end    <- liftIO $ Clock.getTime Clock.Monotonic
      printInfo $ "No programs synthesised - Timeout after: " <> (show timeoutLim  <> "ms")
      return []
  return fin
  
  where

      loop resourceScheme (elimMax, introMax) index defs grade gamma agg = do 

--      Diagonal search
        -- let diagonal = runOmega $ liftM2 (,) (each [0..elimMax]) (each [0..introMax]) 

--      Rectilinear search
        let norm (x,y) = sqrt (fromIntegral x^2+fromIntegral y^2)
        let mergeByNorm = Ordered.mergeAllBy (comparing norm)
        let rectSwap = mergeByNorm (map mergeByNorm [[[(x,y) | x <- [0..elimMax]] | y <- [0..introMax]]])

        let lims = rectSwap



        pRes <- foldM (\acc (elim, intro) -> 
          case acc of 
            (Just res, agg') -> return (Just res, agg')
            (Nothing, agg')  -> do 
              putStrLn $  "elim: " <> (show elim) <> " intro: " <> (show intro)   
              let synRes = synthesise resourceScheme gamma (Focused []) (Depth elim 0 intro) grade (Goal goalTy $ Just NonDecreasing)
              (res, agg'') <- runStateT (runSynthesiser index synRes checkerState) (resetState agg')
              if (not $ solved res) && (depthReached agg'') then return (Nothing, agg'') else return (Just res, agg'')
          ) (Nothing, agg) lims
        case pRes of 
          (Just finRes, finAgg) -> do 
            return (finRes, finAgg)
          (Nothing, finAgg) -> loop resourceScheme (elimMax, introMax) index defs grade gamma finAgg 
 

      solved res = case res of ((Right (expr, _, _), _):_) -> True ; _ -> False
      resetState st = st { depthReached = False }



      -- eval takes an unnanotaed AST, so we need to strip out annotations in order to stitch our synthed expr back into
      -- the original AST. Why do we not synthesise unannotated exprs directly? It's possible we may want to use the type
      -- info in the future.
      unannotateExpr :: Expr () Type -> Expr () ()
      unannotateExpr (App s a rf e1 e2)             = App s () rf (unannotateExpr e1) $ unannotateExpr e2
      unannotateExpr (AppTy s a rf e1 t)            = AppTy s () rf (unannotateExpr e1) t
      unannotateExpr (Binop s a b op e1 e2)         = Binop s () b op (unannotateExpr e1) $ unannotateExpr e2
      unannotateExpr (LetDiamond s a b ps mt e1 e2) = LetDiamond s () b (unannotatePat ps) mt (unannotateExpr e1) $ unannotateExpr e2
      unannotateExpr (TryCatch s a b e p mt e1 e2)  = TryCatch s () b (unannotateExpr e) (unannotatePat p) mt (unannotateExpr e1)  $ unannotateExpr e2
      unannotateExpr (Val s a b val)                = Val s () b (unannotateVal val)
      unannotateExpr (Case s a b expr pats)         = Case s () b (unannotateExpr expr) $ map (\(p, e) -> (unannotatePat p, unannotateExpr e)) pats
      unannotateExpr (Hole s a b ids hints)         = Hole s () b ids hints

    
      unannotateVal :: Value () Type -> Value () ()
      unannotateVal (Abs a p mt e)        = Abs () (unannotatePat p) mt $ unannotateExpr e
      unannotateVal (Promote a e)         = Promote () $ unannotateExpr e
      unannotateVal (Pure a e)            = Pure () $ unannotateExpr e
      unannotateVal (Nec a e)             = Nec () $ unannotateExpr e
      unannotateVal (Constr a ident vals) = Constr () ident $ map unannotateVal vals
      unannotateVal (Var a idv)           = Var () idv
      unannotateVal (Ext a ev)            = Ext () ev
      unannotateVal (NumInt n)            = NumInt n
      unannotateVal (NumFloat n)          = NumFloat n
      unannotateVal (CharLiteral c)       = CharLiteral c
      unannotateVal (StringLiteral s)     = StringLiteral s


      unannotatePat :: Pattern Type -> Pattern ()
      unannotatePat (PVar s a rf nm)         = PVar s () rf nm
      unannotatePat (PWild s a rf)           = PWild s () rf
      unannotatePat (PBox s a rf p)          = PBox s () rf $ unannotatePat p
      unannotatePat (PInt s a rf int)        = PInt s () rf int
      unannotatePat (PFloat s a rf doub)     = PFloat s () rf doub
      unannotatePat (PConstr s a rf nm pats) = PConstr s () rf nm $ map unannotatePat pats


  

useBinderNameOrFreshen :: Maybe Id -> Synthesiser Id
useBinderNameOrFreshen Nothing = freshIdentifier
useBinderNameOrFreshen (Just n) = return n

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

elapsedTime :: TimeSpec -> TimeSpec -> Integer
elapsedTime start end = round $ fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double)

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












synthesiseGradedBase :: (?globals :: Globals) 
  => Maybe Hints 
  -> Int 
  -> Ctxt TypeScheme  -- Unrestricted Defs 
  -> Ctxt (TypeScheme, Type) -- Restricted Defs
  -> Id
  -> Ctxt Assumption    -- (unfocused) free variables
  -> TypeScheme           -- type from which to synthesise
  -> CheckerState
  -> IO [Expr () ()]
synthesiseGradedBase hints index unrestricted restricted currentDef ctxt goal cs = do

  start <- liftIO $ Clock.getTime Clock.Monotonic
  let checkerState = initState { tyVarContext = [(v, (k, ForallQ)) | (v, k) <- [(mkId "a", ktype), (mkId "b", ktype)]] }
  let synthState = SynthesisData {
                         smtCallsCount= 0 
                      ,  smtTime= 0 
                      ,  proverTime= 0 
                      ,  theoremSizeTotal= 0 
                      ,  pathsExplored= 0 
                      ,  startTime=start 
                      ,  constructors=[] 
                      ,  currDef = []
                      ,  depthReached = False
                      }


  {-

  f :: a ^ 1 -> (a ^ 1 -> b) -> b)
  
  -}

  -- let goalTy = FunTy Nothing (Just $ TyGrade Nothing 1) (TyVar $ mkId "a") (TyVar $ mkId "a")
  let goalTy = FunTy Nothing (Just $ TyGrade Nothing 1) (TyVar $ mkId "a") (FunTy Nothing (Just $ TyGrade Nothing 1) (FunTy Nothing (Just $ TyGrade Nothing 1) (TyVar $ mkId "a") (TyVar $ mkId "b")) (TyVar $ mkId "b"))

  -- let datadecls = []


  let initRes = gSynthInner RightAsync [] (Focused []) goalTy
  result <- liftIO $ do 
    (res, agg) <- runStateT (runSynthesiser 1 initRes checkerState) synthState 
    return (res, agg)

  

  fin <- case result of 
      (synthResult, _) -> do
        let programs = nub $ map fst3 $ rights (map fst synthResult)
        return programs
  return fin



gSynthInner :: (?globals :: Globals) => FocusPhase -> Ctxt SAssumption -> FocusedCtxt SAssumption -> Type -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution)
gSynthInner focusPhase gamma (Focused omega) goal = do

  debugM "reached here" (show gamma)


  case (focusPhase, omega) of 
    (RightAsync, _) -> do
      varRule [] (Focused []) (Focused (gamma ++ omega)) goal
      `try`
      absRule RightAsync gamma (Focused omega) goal
      `try`
      transitionToLeftAsync gamma omega goal 

    (LeftAsync, (_:_)) -> do 
      varRule gamma (Focused []) (Focused omega) goal
      `try`
      unboxRule LeftAsync gamma (Focused []) (Focused omega) goal

    -- Focus / shift to Sync phases 
    (LeftAsync, []) -> do 
      foc goal gamma $ isRAsync goal

    (RightSync, []) -> 
      if isRSync goal then do
        varRule gamma (Focused []) (Focused omega) goal
        `try`
        boxRule RightSync gamma goal
      else do
        gSynthInner RightAsync gamma (Focused []) goal
    
    (LeftSync, var@(x, SVar (Discharged ty g) _):[]) -> do 
      if (not $ isLSync ty) && (not $ isAtomic ty) then do 
        gSynthInner LeftAsync gamma (Focused [var]) goal
      else do
        varRule gamma (Focused []) (Focused omega) goal
        `try`
        appRule LeftSync gamma (Focused []) (Focused omega) goal
    
    (LeftSync, []) -> 
      gSynthInner RightAsync gamma (Focused []) goal

  where 

    foc goal gamma True = 
      focRight gamma goal 
      `try`
      focLeft [] gamma goal
    foc goal gamma False = 
      focLeft [] gamma goal 

    focRight gamma goal = 
      gSynthInner RightSync gamma (Focused []) goal 

    focLeft _ [] goal = none 
    focLeft left (var:right) goal = 
      focLeft (var:left) right goal 
      `try`
      gSynthInner LeftSync (left ++ right) (Focused [var]) goal

    transitionToLeftAsync _ _ (FunTy{}) = none
    transitionToLeftAsync gamma omega goal = gSynthInner LeftAsync gamma (Focused omega) goal




{- 

--------------------------------- Var
Γ, x :ᵣ A ⊢ A => x | 0·Γ, x :₁ A

-}
varRule :: (?globals :: Globals) => Ctxt SAssumption -> FocusedCtxt SAssumption -> FocusedCtxt SAssumption -> Type -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution)
varRule _ _ (Focused []) _ = none
varRule gamma (Focused left) (Focused (var@(name, SVar (Discharged t grade) sInfo) : right)) goal = do
  varRule gamma (Focused (var:left)) (Focused right) goal `try` do
    conv $ resetAddedConstraintsFlag 
    (success, _, subst) <- conv $ equalTypes ns t goal 

    cs <- conv $ get
    modifyPred $ addPredicateViaConjunction (Conj $ predicateStack cs) (predicateContext cs)
    conv $ modify (\s -> s { predicateStack = []}) 

    if success then do 
      solved <- if addedConstraints cs
                then solve
                else return True
      -- now to do check we can actually use it
      if solved then do
        (kind, _, _) <- conv $ synthKind ns grade
        delta <- ctxtMultByCoeffect (TyGrade (Just kind) 0) (left ++ right ++ gamma) 
        let singleUse = (name, SVar (Discharged t (TyGrade (Just kind) 1)) sInfo)
        return (Val ns () False (Var () name), singleUse:delta, subst)
      else none
    else none
varRule _ _ _ _ = none


{- 

Γ, x :ᵣ A ⊢ B => t | Δ, x :ᵣ A      r ⊑ q
-------------------------------------------- Abs
Γ ⊢ Aʳ → B => λᵣx.t | Δ 

-}
absRule :: (?globals :: Globals) => FocusPhase -> Ctxt SAssumption -> FocusedCtxt SAssumption -> Type -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution)
absRule focusPhase gamma (Focused omega) (FunTy name (Just grade) tyA tyB) = do

  x <-  useBinderNameOrFreshen name

  let (gamma', omega') = bindToContext (x, SVar (Discharged tyA grade) (Just NonDecreasing)) gamma omega (isLAsync tyA)

  (t, delta, subst) <- gSynthInner focusPhase gamma' (Focused omega') tyB

  case lookupAndCutout x delta of 
    Just (delta', SVar (Discharged _ grade_r) _) -> do 
      cs <- conv $ get
      (kind, _, _) <- conv $ synthKind nullSpan grade_r
      modifyPred $ addConstraintViaConjunction (ApproximatedBy ns grade_r grade kind) (predicateContext cs)
      res <- solve
      boolToSynthesiser res (Val ns () False (Abs () (PVar ns () False x) Nothing t), delta', subst)
    Nothing -> none

absRule _ _ _ _ = none


{- 

Γ, x :_r1 A^q → B, y :_r2 B ⊢ C => t₁ | Δ₁, x :_s1 A^q → B, y :_s2 B
Γ, x :_r1 A^q → B ⊢ A => t₂ | Δ₂, x :_s3 : A^q → B
----------------------------------------------------------------------------------------------:: app
Γ, x : A → B ⊢ C => [(x t₂) / y] t₁ | (Δ₁ + s2 · q · Δ₂), x :_s2 + s1 + (s2 · q · s3) A^q → B

-}
appRule :: (?globals :: Globals) => FocusPhase -> Ctxt SAssumption -> FocusedCtxt SAssumption -> FocusedCtxt SAssumption -> Type -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution)
appRule _ _ _ (Focused []) _ = none
appRule focusPhase gamma (Focused left) (Focused (var@(x1, SVar (Discharged (FunTy bName (Just q) tyA tyB) r) sInfo) : right)) goal = 
  appRule focusPhase gamma (Focused (var : left)) (Focused right) goal `try` do 

    debugM "reached" (show x1)

    let omega = (left ++ right)
    x2 <- freshIdentifier

    let (gamma', omega') = bindToContext (x2, SVar (Discharged tyB r) Nothing) (var:gamma) omega (isLAsync tyB)

    (t1, delta1, subst1) <- gSynthInner focusPhase gamma' (Focused omega') goal

    case lookupAndCutout x2 delta1 of 
      Just (delta1', SVar (Discharged _ s2) _) -> 
        case lookupAndCutout x1 delta1' of 
          Just (delta1'', SVar (Discharged _ s1) _) ->
            do
              (t2, delta2, subst2) <- gSynthInner RightSync (var:gamma) (Focused omega) tyA
              case lookupAndCutout x1 delta2 of 
                Just (delta2', SVar (Discharged _ s3) _) -> do
                  -- let outputDelta = delta1'' `ctxtAdd` (s2 `ctxtMultByCoeffect` (q `ctxtMultByCoeffect` delta2))
                  outputDelta2 <- (s2 `ctxtMultByCoeffect` delta2) >>= (\delta2' -> (q `ctxtMultByCoeffect` delta2')) 
                  let outputGrade = s2 `gPlus` s1 `gPlus` (s2 `gTimes` q `gTimes` s3) 
                  case ctxtAdd delta1'' outputDelta2 of 
                    Just delta3 -> do 
                      
                      substOut <- conv $ combineSubstitutions ns subst1 subst2
                      let appExpr = App ns () False (Val ns () False (Var () x1)) t2
                      return (Language.Granule.Syntax.Expr.subst appExpr x2 t1, (x1, SVar (Discharged (FunTy bName (Just q) tyA tyB) outputGrade) sInfo):delta3, substOut)
                    _ -> none                    
                    -- s2 + s1 + (s2 * q * s3)
          _ -> none
      _ -> none

appRule _ _ _ _ _ = none

{-


Γ ⊢ A => t | Δ
------------------------ :: box
Γ ⊢ □ᵣA => [t] | r · Δ

-}
boxRule :: (?globals :: Globals) => FocusPhase -> Ctxt SAssumption -> Type -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution)
boxRule focusPhase gamma (Box grade_r goal) = do 
  (t, delta, subst) <- gSynthInner focusPhase gamma (Focused []) goal
  delta' <- ctxtMultByCoeffect grade_r delta
  let boxExpr = Val ns () False (Promote () t)
  return (boxExpr, delta', subst)
boxRule _ _ _ = none


{-

Γ, y :_r·q A, x :_r □q A ⊢ B => t | Δ, y : [A] s1, x :_s2 □q A 
∃s3 . s1 ⊑ s3 · q ⊑ r · q
---------------------------------------------------------------- :: unbox
Γ, x :_r □q A ⊢ B => case x of [y] -> t | Δ, x :_s3+s2 □q A

-}
unboxRule :: (?globals :: Globals) => FocusPhase -> Ctxt SAssumption -> FocusedCtxt SAssumption -> FocusedCtxt SAssumption -> Type -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution) 
unboxRule _ _ _ (Focused []) _ = none
unboxRule focusPhase gamma (Focused left) (Focused (var_x@(x, SVar (Discharged (Box grade_q ty) grade_r) sInfo):right)) goal = 
  unboxRule focusPhase gamma (Focused (var_x:left)) (Focused right) goal `try` do 

    let omega = (left ++ right)
    y <- freshIdentifier 

    let (gamma', omega') = bindToContext (y, SVar (Discharged ty (grade_r `gTimes` grade_q)) Nothing) (var_x:gamma) omega (isLAsync ty)

    (t, delta, subst) <- gSynthInner focusPhase gamma' (Focused omega') goal 

    case lookupAndCutout y delta of 
      Just (delta', SVar (Discharged _ grade_s1) _) -> 
        case lookupAndCutout x delta' of 
          Just (delta'', SVar (Discharged _ grade_s2) _) -> do
            cs <- conv get

            grade_id_s3 <- freshIdentifier 
            (kind, _, _) <- conv $ synthKind nullSpan grade_s1
            conv $ existentialTopLevel grade_id_s3 kind

            let grade_s3 = TyVar grade_id_s3
            -- ∃s3 . s1 ⊑ s3 · q ⊑ r · q
            modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (grade_s3 `gTimes` grade_q) (grade_r `gTimes` grade_q) kind) (predicateContext cs)
            modifyPred $ addConstraintViaConjunction (ApproximatedBy ns grade_s1 (grade_s3 `gTimes` grade_q) kind) (predicateContext cs)
            
            res <- solve 

            let var_x' = (x, SVar (Discharged (Box grade_q ty) (grade_s3 `gPlus` grade_s2)) sInfo)

            boolToSynthesiser res ((makeUnboxUntyped y (makeVarUntyped x) t), var_x':delta'', subst)
          _ -> none
      _ -> none



{-

(C: B₁^q₁ → ... → Bₙ^qₙ → K A ∈ D)
Γ ⊢ Bᵢ => tᵢ | Δᵢ
----------------------------------------------------:: constr
Γ ⊢ K A => C t₁ ... tₙ | (q₁ · Δ₁) + ... + (qₙ · Δₙ)

-}
constrRule :: (?globals :: Globals) => FocusPhase -> Ctxt SAssumption -> Type -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution)
constrRule focusPhase gamma goal = 
  case isADTorGADT goal of 
    Just datatypeName -> do 
      synthState <- getSynthState 
      let (_, datacons) = relevantConstructors datatypeName $ constructors synthState
      let datacons' = sortBy compareArity datacons

      tryDatacons datatypeName [] datacons' goal

  
  where 
    tryDatacons dtName _ [] _ = none
    tryDatacons dtName right (con@(cName, (tySc@(Forall s bs cs cTy), cSubst)):left) goal = 
      tryDatacons dtName (con:right) left goal `try` do
        result <- checkConstructor False tySc goal cSubst 
        case result of 
          (True, specTy, _, _, _) -> do
            case dataconArgs specTy of 
              -- Nullary constructor 
              Just [] -> return (Val ns () False (Constr () cName []), [], [])
              -- N-ary constructor
              Just args -> do 
                (ts, delta, subst) <- synthArgs args 
                return (makeConstrUntyped ts dtName, delta, subst)
          _ -> none

    synthArgs [] = return ([], [], [])
    synthArgs ((ty, mGrade_q):args) = do 
      (ts, deltas, substs) <- synthArgs args
      (t, delta, subst) <- gSynthInner RightAsync gamma (Focused []) goal
      delta' <- maybeToSynthesiser $ ctxtAdd deltas delta
      substs' <- conv $ combineSubstitutions ns substs subst
      delta'' <- case mGrade_q of 
        Just grade_q -> ctxtMultByCoeffect grade_q delta'
        _ -> return delta' 
      return (t:ts, delta'', substs')

    dataconArgs (TyCon _) = Just []
    dataconArgs (TyApp _ _) = Just []
    dataconArgs (FunTy _ mGrade_q tyA tyB) = do 
      res <- dataconArgs tyB
      return $ (tyA, mGrade_q) : res 
    dataconArgs _ = Nothing 


{-

(C: B₁^q₁ → ... → Bₙ^qₙ → K A ∈ D)
Γ, x :ᵣ K A, y₁ⁱ :_q₁ B₁ ... yₙⁱ :_qₙ Bₙ ⊢ B => tᵢ | Δᵢ, x :_rᵢ K A, y₁ⁱ :_s₁ⁱ B₁ ... yₙⁱ :_sₙⁱ Bₙ
∃s'ⱼⁱ . sⱼⁱ ⊑ s'ⱼⁱ · qⱼⁱ ⊑ r · qⱼⁱ
sᵢ = s'₁ⁱ ⊔ ... ⊔ s'ₙⁱ
--------------------------------------------------------------------------------------------------------:: case (v1)
Γ, x :ᵣ K A ⊢ B => case x of cᵢ y₁ⁱ ... yₙⁱ -> tᵢ | (Δ₁ ⊔ ... ⊔ Δₙ), x :_(r₁ ⊔ ... ⊔ rₙ)+(s₁ ⊔ ... ⊔ sₙ)

-}
caseRule :: (?globals :: Globals) => FocusPhase -> Ctxt SAssumption -> FocusedCtxt SAssumption -> FocusedCtxt SAssumption -> Type -> Synthesiser (Expr () (), Ctxt SAssumption, Substitution)
caseRule _ _ _ (Focused []) _ = none
caseRule focusPhase gamma (Focused left) (Focused (var@(x, SVar (Discharged ty grade_r) sInfo):right)) goal = 
  caseRule focusPhase gamma (Focused (var : left)) (Focused right) goal `try` do
    case isADTorGADT ty of 
      Just datatypeName -> do
        let omega = left ++ right
        synthState <- getSynthState

        let (_, nonRecCons) = relevantConstructors datatypeName (constructors synthState)
        let datacons = sortBy compareArity nonRecCons

        (patExprs, delta, subst, grade_r_out, grade_s_out, _) <- foldM (\ (exprs, deltas, substs, mGrade_r_out, mGrade_s_out, index) con@(cName, (tySc@(Forall s bs cs cTy), cSubst)) -> do

          cs <- conv get
          let pred = newImplication [] (predicateContext cs)

          result <- checkConstructor True tySc ty cSubst 
          let predSucceeded = moveToConsequent pred

          case (result, predSucceeded) of 
            ((True, specTy, args, _, _), Right pred'@(ImplConsequent ctxt p path)) -> do 
              modifyPred pred'

              (gamma', omega', varsAndGrades) <- foldM (\(gamma, omega, vars) (arg, mGrade_q) -> do 
                  y <- freshIdentifier
                  let grade_rq = case mGrade_q of 
                        Just grade_q -> grade_r `gTimes` grade_q
                        Nothing -> grade_r

                  let assumption = (y, SVar (Discharged arg grade_rq) Nothing)
                  let (gamma', omega') = bindToContext assumption gamma omega (isLAsync arg)
                  return (gamma', omega', (y, grade_rq):vars)
                ) (gamma, omega, []) args
              let (vars, _) = unzip varsAndGrades
              let constrPat = PConstr ns () False cName (map (PVar ns () False) vars)

              (t, delta, subst) <- gSynthInner focusPhase (var:gamma') (Focused omega') goal 

              (delta', grade_si) <- foldM (\(delta', mGrade) dVar@(dName, SVar (Discharged ty grade_s) dSInfo) -> 
                case lookup dName varsAndGrades of 
                  Just grade_rq -> do 
                    cs <- conv get 

                    grade_id_s' <- freshIdentifier 
                    (kind, _, _) <- conv $ synthKind ns grade_s 
                    conv $ existentialTopLevel grade_id_s' kind
                    let grade_s' = TyVar grade_id_s'

                    -- ∃s'_ij . s_ij ⊑ s'_ij · q_ij ⊑ r · q_ij
                    modifyPred $ addConstraintViaConjunction (ApproximatedBy ns (grade_s' `gTimes` grade_rq) (grade_r `gTimes` grade_r) kind) (predicateContext cs)
                    modifyPred $ addConstraintViaConjunction (ApproximatedBy ns grade_s (grade_s' `gTimes` grade_rq) kind) (predicateContext cs)

                    res <- solve

                    -- s' \/ ...
                    let grade_si = case mGrade of 
                            Just s -> s `gJoin` grade_s'
                            Nothing -> grade_s'

                    return (delta', Just grade_si)
                  _ -> return (dVar:delta', mGrade)
                ) ([], Nothing) delta

              case (lookupAndCutout x delta', grade_si) of 
                (Just (delta'', (SVar (Discharged _ grade_r') sInfo)), Just grade_si') -> do

                  returnDelta <- if index == 0 then return delta' else ctxtMerge (TyInfix TyOpJoin) deltas delta' 
                  returnSubst <- conv $ combineSubstitutions ns subst substs

                  modifyPred $ moveToNewConjunct (predicateContext cs)

                  let grade_r_out' = case mGrade_r_out of 
                        Just g -> g `gJoin` grade_r'
                        Nothing -> grade_r'

                  let grade_s_out' = case mGrade_s_out of 
                        Just s -> s `gJoin` grade_si'
                        Nothing -> grade_si'

                  return ((constrPat, t):exprs, returnDelta, returnSubst, Just grade_r_out', Just grade_s_out', index+1)

                _ -> do 
                  modifyPred $ moveToNewConjunct (predicateContext cs)
                  return (exprs, deltas, substs, mGrade_r_out, mGrade_s_out, index)
            _ -> do 
              modifyPred $ moveToNewConjunct (predicateContext cs)
              return (exprs, deltas, substs, mGrade_r_out, mGrade_s_out, index)
          ) ([], [], [], Nothing, Nothing, 0) datacons 

        case (patExprs, grade_r_out, grade_s_out) of 
          ((_:_), Just grade_r_out', Just grade_s_out') -> do 
            let var_x_out = (x, SVar (Discharged ty (grade_r_out' `gPlus` grade_s_out')) sInfo)
            return (makeCaseUntyped x patExprs, var_x_out:delta, subst)
          _ -> none
      _ -> none





caseRule _ _ _ _ _ = none



gPlus :: Type -> Type -> Type
gPlus g1 g2 = TyInfix TyOpPlus g1 g2

gTimes :: Type -> Type -> Type
gTimes g1 g2 = TyInfix TyOpTimes g1 g2

gJoin :: Type -> Type -> Type
gJoin g1 g2 = TyInfix TyOpJoin g1 g2




exprFold :: Span -> Expr () () -> Expr () () -> Expr () ()
exprFold s newExpr (App s' a rf e1 e2) = (App s' a rf (exprFold s newExpr e1) (exprFold s newExpr e2))
exprFold s newExpr (AppTy s' a rf e1 t) = (AppTy s' a rf (exprFold s newExpr e1) t)
exprFold s newExpr (Binop s' a b op e1 e2) = (Binop s' a b op (exprFold s newExpr e1) (exprFold s newExpr e2))
exprFold s newExpr (LetDiamond s' a b ps mt e1 e2) = (LetDiamond s' a b ps mt (exprFold s newExpr e1) (exprFold s newExpr e2))
exprFold s newExpr (TryCatch s' a b e p mt e1 e2) = (TryCatch s' a b (exprFold s newExpr e) p mt (exprFold s newExpr e1) (exprFold s newExpr e2))
exprFold s newExpr (Val s' a b val) = (Val s' a b (valueFold s newExpr val))
exprFold s newExpr (Case s' a b expr pats) = (Case s' a b (exprFold s newExpr expr) pats)
exprFold s newExpr (Hole s' a b ids hints) = if s == s' then newExpr else (Hole s' a b ids hints)

    
valueFold :: Span -> Expr () () -> Value () () -> Value () ()
valueFold s newExpr (Abs a pats mt e) = (Abs a pats mt (exprFold s newExpr e))
valueFold s newExpr (Promote a e) = (Promote a (exprFold s newExpr e))
valueFold s newExpr (Pure a e) = (Pure a (exprFold s newExpr e))
valueFold s newExpr (Nec a e) = (Nec a (exprFold s newExpr e))
valueFold s newExpr (Constr a ident vals) = (Constr a ident $ map (valueFold s newExpr) vals)
valueFold s newExpr v = v 