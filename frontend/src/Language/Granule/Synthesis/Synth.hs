{-# LANGUAGE ImplicitParams #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}


{-# options_ghc -fno-warn-incomplete-uni-patterns #-}
module Language.Granule.Synthesis.Synth where

import qualified Data.Map as M

import Data.List (sortBy,nub)

import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
import Control.Monad.Logic
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
import Language.Granule.Checker.Variables
    ( freshIdentifierBase, freshTyVarInContext )
import Language.Granule.Synthesis.Builders
import Language.Granule.Synthesis.Monad

import Data.Either (rights)
import Control.Monad.State.Strict

import qualified Control.Monad.State.Strict as State (get)
import qualified System.Clock as Clock
-- import qualified Control.Monad.Memo as Memo
import qualified System.Timeout
import qualified Data.List.Ordered as Ordered

import Language.Granule.Utils
import Data.Maybe (fromJust, catMaybes, fromMaybe, maybeToList)
import Control.Arrow (second)
-- import Control.Monad.Omega
import System.Clock (TimeSpec)

import Data.Ord


{-- SYNTHESIS

    This module implements Granule's synthesis tool, following a top-down backwards style proof-search
    with focusing and interative deepening, parameterised by a resource management scheme. See LOPSTR 
    2020 paper for an overview of the additive, additive pruning and subtractive schemes. By default, 
    the additive resource management scheme is used.

--}

data PruningScheme = NonPruning | Pruning
  deriving (Show, Eq)

data ResourceScheme a = Additive a | Subtractive
  deriving (Show, Eq)

type Bindings = [(Id, (Id, Type))]

data Goal = Goal TypeScheme Structure
  deriving (Show, Eq)

newtype FocusingContext a = FocusingContext (Ctxt a)

data Depth = Depth 
  {
    eMax    :: Int  -- Maximum number of eliminations (of recursive data structures) allowed
  , iCurr   :: Int  -- Current level of eliminations (of recursive data structures)
  , iMax    :: Int  -- Maximum number of introductions (of recursive data structures) allowed
  , appMax  :: Int  -- Maximum number of nested applications allowed
  }
  deriving (Show, Eq)

data Structure = None | NonDecreasing | Decreasing
  deriving (Show, Eq, Ord)

data AssumptionInfo = AInfo Structure Int
  deriving (Show, Eq, Ord)

data FocusPhase = Focus RightLeft AsyncSync       
  deriving (Show, Eq)
data RightLeft = R | L
  deriving (Show, Eq)
data AsyncSync = Async | Sync
  deriving (Show, Eq)


solve :: (?globals :: Globals)
  => Synthesiser Bool
solve = do
  cs <- conv State.get
  -- let pred = Conj $ predicateStack cs
  tyVars <- conv $ includeOnlyGradeVariables nullSpanNoFile (tyVarContext cs)

  st <- conv get 

  let pred = fromPredicateContext (predicateContext st)
  debugM "synthDebug" ("SMT on pred = " ++ pretty pred)


  -- 
  -- tyVars <- conv $ tyVarContextExistential >>= includeOnlyGradeVariables nullSpanNoFile
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

-- * Context manipulations

ctxtSubtract :: (?globals :: Globals) => Ctxt (Assumption, AssumptionInfo)  -> Ctxt (Assumption, AssumptionInfo) -> Synthesiser (Ctxt (Assumption, AssumptionInfo))
ctxtSubtract gam [] = return gam
ctxtSubtract gam ((x, (Linear t, _)):del) =
  case lookupAndCutout x gam of
    Just (gam', _) -> ctxtSubtract gam' del
    Nothing -> none

ctxtSubtract gam ((x, (Discharged t g2, _)):del) =
  case lookupAndCutout x gam of
    Just (gam', (Discharged t2 g1, info)) -> do
      g3 <- g1 `gradeSub` g2
      ctx <- ctxtSubtract gam' del
      return ((x, (Discharged t g3, info)):ctx)
    _ -> none
    where
      gradeSub g g' = do
        -- g - g' = c
        -- therefore
        -- g = c + g'
        (kind, _, _) <- conv $ synthKind nullSpan g
        var <- conv $ freshTyVarInContext (mkId "c") kind
        conv $ existentialTopLevel var kind
        s <- conv get
        modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar var) g') g kind) (predicateContext s)
        -- maximality
        varOther' <- conv $ freshIdentifierBase "cOther"
        let varOther = mkId varOther'
        conv $ addPredicate (Impl [(varOther, kind)]
                                (Conj [Con $ ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar varOther) g') g kind])
                                (Conj [Con $ ApproximatedBy nullSpanNoFile (TyVar varOther) (TyVar var) kind]))
        return $ TyVar var

ctxtMultByCoeffect :: Type -> Ctxt (Assumption, AssumptionInfo) -> Synthesiser (Ctxt (Assumption, AssumptionInfo))
ctxtMultByCoeffect _ [] = return []
ctxtMultByCoeffect g1 ((x, (Discharged t g2, info)):xs) = do
      ctxt <- ctxtMultByCoeffect g1 xs
      return ((x, (Discharged t (TyInfix TyOpTimes g1 g2), info)): ctxt)
ctxtMultByCoeffect _ _ = none

ctxtDivByCoeffect :: (?globals :: Globals) => Type -> Ctxt (Assumption, AssumptionInfo) -> Synthesiser (Ctxt (Assumption, AssumptionInfo))
ctxtDivByCoeffect _ [] = return []
ctxtDivByCoeffect g1 ((x, (Discharged t g2, info)):xs) =
    do
      ctxt <- ctxtDivByCoeffect g1 xs
      var <- gradeDiv g1 g2
      return ((x, (Discharged t var, info)): ctxt)
  where
    gradeDiv g g' = do
      (kind, _, _) <- conv $ synthKind nullSpan g
      var <- conv $ freshTyVarInContext (mkId "c") kind
      conv $ existentialTopLevel var kind
      s <- conv get
      modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyInfix TyOpTimes g (TyVar var)) g' kind) (predicateContext s)
      return $ TyVar var
ctxtDivByCoeffect _ _ = none

ctxtMerge :: (?globals :: Globals)
          => (Type -> Type -> Type) -- lattice operator
          -> Ctxt (Assumption, AssumptionInfo)
          -> Ctxt (Assumption, AssumptionInfo)
          -> Synthesiser (Ctxt (Assumption, AssumptionInfo))

-- Base cases
--  * Empties
ctxtMerge _ [] [] = return []

--  * Can meet/join an empty context to one that has graded assumptions
ctxtMerge operator [] ((x, (Discharged t g, info)) : ctxt) = do
  -- Left context has no `x`, so assume it has been weakened (0 gade)
--  (kind, _, _) <- conv $ synthKind nullSpan g
  ctxt' <- ctxtMerge operator [] ctxt
  return $ (x, (Discharged t g, info)) : ctxt'
--  return $ (x, Discharged t (operator (TyGrade (Just kind) 0) g)) : ctxt'

--  * Cannot meet/join an empty context to one with linear assumptions
ctxtMerge operator [] ((x, (Linear t, info)) : ctxt) = do
  ctxt' <- ctxtMerge operator [] ctxt
  return $ ((x, (Linear t, info)) : ctxt')
  

-- Inductive cases
ctxtMerge operator ((x, (Discharged t1 g1, info)) : ctxt1') ctxt2 =
  case lookupAndCutout x ctxt2 of
    Just (ctxt2', (Discharged t2 g2, info)) ->
      if t1 == t2 -- Just in case but should always be true
        then do
          ctxt' <- ctxtMerge operator ctxt1' ctxt2'
          return $ (x, (Discharged t1 (operator g1 g2), info)) : ctxt'

        else none

    Just (_, (Linear _, _)) -> none -- mode mismatch

    Nothing -> do
      -- Right context has no `x`, so assume it has been weakened (0 gade)
      ctxt' <- ctxtMerge operator ctxt1' ctxt2
      return $ (x, (Discharged t1 g1, info)) : ctxt'
      --return $ (x, Discharged t1 (operator g1 (TyGrade (Just kind) 0))) : ctxt'

ctxtMerge operator ((x, (Linear t1, info)) : ctxt1') ctxt2 =
  case lookupAndCutout x ctxt2 of
    Just (ctxt2', (Linear t2, info)) ->
      if t1 == t2 -- Just in case but should always be true
        then do
          ctxt' <- ctxtMerge operator ctxt1' ctxt2'
          return $ (x, (Linear t1, info)) : ctxt1'
        else none

    Just (_, (Discharged{}, _)) -> none -- mode mismatch

    Nothing -> none -- Cannot weaken a linear thing

ctxtAdd :: Ctxt (Assumption, AssumptionInfo) -> Ctxt (Assumption, AssumptionInfo) -> Maybe (Ctxt (Assumption, AssumptionInfo))
ctxtAdd [] y = Just y
ctxtAdd ((x, (Discharged t1 g1, info)):xs) ys =
  case lookupAndCutout x ys of
    Just (ys', (Discharged t2 g2, info')) -> do
      ctxt <- ctxtAdd xs ys'
      return $ (x, (Discharged t1 (TyInfix TyOpPlus g1 g2), info')) : ctxt
    Nothing -> do
      ctxt <- ctxtAdd xs ys
      return $ (x, (Discharged t1 g1, info)) : ctxt
    _ -> Nothing
ctxtAdd ((x, (Linear t1, info)):xs) ys =
  case lookup x ys of
    Just (Linear t2, info') -> Nothing
    Nothing -> do
      ctxt <- ctxtAdd xs ys
      return $ (x, (Linear t1, info)) : ctxt
    _ -> Nothing



bindToContext :: 
     (Id, (Assumption, AssumptionInfo)) 
  -> Ctxt (Assumption, AssumptionInfo) 
  -> Ctxt (Assumption, AssumptionInfo) 
  -> Bool 
  -> (Ctxt (Assumption, AssumptionInfo), Ctxt (Assumption, AssumptionInfo))
bindToContext var gamma omega True = (gamma, var:omega)
bindToContext var gamma omega False = (var:gamma, omega)


isADTorGADT :: Type -> Maybe Id
isADTorGADT (TyCon id) = Just id
isADTorGADT (TyApp e1 e2) = isADTorGADT e1
isADTorGADT _ = Nothing

isRAsync :: Type -> Bool
isRAsync FunTy{} = True
isRAsync _ = False

isRSync :: Type -> Bool
isRSync TyApp{} = True
isRSync TyCon{} = True
isRSync Box{}   = True
isRSync _ = False

isLAsync :: Type -> Bool
isLAsync TyApp{} = True
isLAsync TyCon{} = True
isLAsync Box{}   = True
isLAsync _ = False

isLSync :: Type -> Bool
isLSync FunTy{} = True
isLSync _ = False

isAtomic :: Type -> Bool
isAtomic TyVar {} = True
isAtomic _ = False


{- 

     Given a data constructor, try to unify a fresh instance of this constructor with the assumption type. If the unification generates 
     additional constraints then these are solved locally for that type constructor. 

-}
checkConstructor :: (?globals::Globals)
      => Bool -- Do impossibility check?
      -> TypeScheme 
      -> Type 
      -> Substitution 
      -> Synthesiser (Bool, Type, [Type], Substitution, Substitution)
checkConstructor impossibility con@(Forall  _ binders constraints conTy) assumptionTy subst = do
    conv $ resetAddedConstraintsFlag -- reset the flag that says if any constraints were added
    (conTyFresh, tyVarsFreshD, substFromFreshening, constraints', coercions) <- conv $ freshPolymorphicInstance InstanceQ True con subst []

    -- Take the rightmost type of the function type, collecting the arguments along the way 
    let (conTy', args) = rightMostFunTy conTyFresh
    conTy'' <- conv $ substitute coercions conTy'

    -- assumptionTy == conTy 
    (success, specTy, subst') <- conv $ equalTypes nullSpanNoFile assumptionTy conTy''
 
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
 
    -- Run the solver (i.e. to check constraints on type indexes hold)

    -- cs <- conv $ get
    -- debugM "conName: " (pretty $ con)
    -- debugM "predicate: " (pretty $ predicateStack cs)
    -- _ <- if not $ impossibility then error "stop" else return ()
    -- if impossibility && addedConstraints cs then do

    --   let predicate = Conj $ predicateStack cs
    --   predicate <- conv $ substitute subst' predicate
    --   debugM "show predicate: " (pretty predicate)
    --   coeffectVars <- conv $ tyVarContextExistential >>= includeOnlyGradeVariables nullSpanNoFile
    --   --coeffectVars <- conv $ (get >>= (\st -> return $ tyVarContext st)) >>= includeOnlyGradeVariables nullSpanNoFile
    --   constructors <- conv$ allDataConstructorNames
    --   (_, result) <- conv$ liftIO $ provePredicate predicate coeffectVars constructors
    --   let smtResult = case result of QED -> True ; _ -> False
    --   debugM "smt result: " (show smtResult)

    --   --smtResult <- solve  -- use existing solver infrastructure 

    --   return (smtResult, success, specTy, args, subst', substFromFreshening)
    -- else return (True, success, specTy, args, subst', substFromFreshening)


compareArity :: (Id, (TypeScheme, Substitution)) -> (Id, (TypeScheme, Substitution)) -> Ordering
compareArity con1@(_, (Forall _ _ _ ty1, _)) con2@(_, (Forall _ _ _ ty2, _)) = compare (arity ty1) (arity ty2)

compareDecreasing :: (Id, (Assumption, Structure)) -> (Id, (Assumption, Structure)) -> Ordering
compareDecreasing var1@(_, (ty1, structure1)) var2@(_, (ty2 , structure2)) = compare (structure1)  (structure2)

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
    markRecursiveType' tyCon (FunTy _ t1 t2) onLeft = do
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
    constrArgIds (FunTy _ e1 e2) = do
      res <- constrArgIds e2
      return $ e1 : res
    constrArgIds _ = Nothing


isDecreasing :: Id -> [Type] -> Bool
isDecreasing id1 [] = False 
isDecreasing id1 ((TyCon id2):tys) = if id1 == id2 then True else isDecreasing id1 tys
isDecreasing id1 ((Box _ t):tys)   = isDecreasing id1 (t:tys)
isDecreasing id1 ((FunTy _ t1 t2):tys) = isDecreasing id1 (t1:t2:tys) 
isDecreasing id1 ((TyApp t1 t2):tys)   = isDecreasing id1 (t1:t2:tys)
isDecreasing id1 (x:xs) = isDecreasing id1 xs




-- | Get the right most of a function type and collect its arguments in a list
rightMostFunTy :: Type -> (Type, [Type])
rightMostFunTy (FunTy _ arg t) = let (t', args) = rightMostFunTy t in (t', arg : args)
rightMostFunTy t = (t, [])





-- Note that the way this is used, the (var, assumption) pair in the first
-- argument is not contained in the provided context (second argument)
useVar :: (?globals :: Globals)
  => (Id, (Assumption, AssumptionInfo))
  -> Ctxt (Assumption, AssumptionInfo)
  -> ResourceScheme PruningScheme
  -> Maybe Type -- Grade on rule style of synthesis 
  -> Synthesiser (Bool, Ctxt (Assumption, AssumptionInfo), Type)
-- Subtractive
useVar (name, (Linear t, _)) gamma Subtractive _ = return (True, gamma, t)
useVar (name, (Discharged t grade, info)) gamma Subtractive Nothing = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  var <- freshIdentifier 
  conv $ existentialTopLevel var kind -- Existentials must be at the topLevel because they may be generated inside an implication but may occur outside of the implication 
  st <- conv get
  modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar var) (TyGrade (Just kind) 1)) grade kind) (predicateContext st)
  res <- solve
  if res then
    return (True, replace gamma name (Discharged t (TyVar var), info), t) else
    return (False, [], t)
useVar (name, (Discharged t grade, info)) gamma Subtractive (Just grade') = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  var <- freshIdentifier -- conv $ freshTyVarInContext (mkId "c") kind
  conv $ existentialTopLevel var kind
  st <- conv get
  modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar var) grade') grade kind) (predicateContext st)
  res <- solve
  if res then
    return (True, replace gamma name (Discharged t (TyVar var), info), t) else
    return (False, [], t)

-- Additive
useVar (name, (Linear t, info)) _ Additive{} _ = return (True, [(name, (Linear t, info))], t)
useVar (name, (Discharged t grade, info)) _ Additive{} Nothing = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  return (True, [(name, (Discharged t (TyGrade (Just kind) 1), info))], t)
useVar (name, (Discharged t grade, info)) _ Additive{} (Just grade') = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  return (True, [(name, (Discharged t grade', info))], t)


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
  => Ctxt (Assumption, AssumptionInfo)
  -> Ctxt (Assumption, AssumptionInfo)
  -> Ctxt (Assumption, AssumptionInfo)
  -> ResourceScheme PruningScheme
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, AssumptionInfo), Substitution, Bindings, Bool)
varHelper gamma left [] _ _ _ = none
varHelper gamma left (assumption@(id, (a, (AInfo structure _))) : right) resourceScheme grade goal@(Goal (goalTySch@(Forall _ _ _ goalTy)) _) =
  varHelper gamma (assumption:left) right resourceScheme grade goal `try` do
    debugM "synthDebug - inside varHelper checking assumption: " (show assumption <> " against goal " <> show goalTy)
    conv $ resetAddedConstraintsFlag -- reset the flag that says if any constraints were added
    (success, specTy, subst) <- conv $ equalTypes nullSpanNoFile (getAssumptionType a) goalTy

    st <- getSynthState
    cs <- conv $ get

    -- Take the constraints generated by the type equality and add these to the synthesis predicate
    modifyPred $ addPredicateViaConjunction (Conj $ predicateStack cs) (predicateContext cs)
    
    -- Clear the checker state predicate
    conv $ modify (\s -> s { predicateStack = []}) 

    if success then do
      -- see if any constraints were added
      cs <- conv $ get
      solved <- if addedConstraints cs
                  then solve
                  else return True
      -- now to do check we can actually use it
      if solved then do
        (canUse, delta, t) <- useVar assumption (gamma ++ (left ++ right)) resourceScheme grade
        debugM "synthDebug - varHelper canUse? " (show canUse)
        boolToSynthesiser canUse (makeVar id goalTySch, delta, subst, [], structure == Decreasing)
      else none
    else none





defHelper :: (?globals :: Globals)
  => Ctxt (TypeScheme, Int)
  -> Ctxt (TypeScheme, Int)
  -> Ctxt (Assumption, AssumptionInfo)
  -> Ctxt (Assumption, AssumptionInfo)
  -> ResourceScheme PruningScheme
  -> Bool
  -> Depth
  -> FocusPhase     
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, AssumptionInfo), Substitution, Bindings, Bool)
defHelper _ [] _ _ _ _ _ _ _ _ = none

defHelper left (def@(x, (defTySch, appDepth)):right) gamma omega Subtractive inDef depth focusPhase grade goal@(Goal goalTySch@(Forall _ binders constraints ty) structure) =
 defHelper (def:left) right gamma omega Subtractive inDef depth focusPhase grade goal `try`
  (case defTySch of
    (Forall _ _ _ (FunTy{})) -> do

      state <- Synthesiser $ lift $ lift $ get

      -- Only try the def if we haven't hit the def allowed depth 
      if True then do -- && (canDef || not (x `elem` currDef state)) then do
        (freshTy, tyVarsFreshD, substFromFreshening, constraints', _) <- conv $ freshPolymorphicInstance InstanceQ False defTySch [] [] 
        case freshTy of 
          (FunTy _ tyA tyB) -> do 
            debugM "synthDebug - (def) in defHelper attempting to use  def: " (pretty def <> " towards goal: " <> pretty goalTySch)

            y <- freshIdentifier
        
            let (gamma', omega') = bindToContext (y, (Linear tyB, AInfo None 0)) gamma omega (isLAsync tyB)
            debugM "gamma': " (show gamma')
            debugM "omega': " (show omega')
            -- let (gamma'', omega'' ) = leftAsyncTransition gamma' omega' ((appCurr depth) + 1 > appMax depth)
            -- _ <- error "asda"

            let def' = (x, (defTySch, appDepth+1))

            (e1, delta1, subst1, bindings1, structurallyDecr1) <- synthesiseInner (def':left ++ right) Subtractive True depth focusPhase gamma' omega' grade goal 
            debugM "gamma': " (show gamma')
            debugM "omega': " (show omega')
            debugM "delta1: " (show delta1)
            -- _ <- error (pretty e1)

            case lookup y delta1 of
              Nothing -> do
           
                (e2, delta2, subst2, bindings2, structurallyDecr2) <- synthesiseInner (def':left ++ right) Subtractive True depth (Focus R Sync) delta1 [] grade (Goal (Forall nullSpanNoFile binders constraints tyA) structure) 


                debugM "synthDebug - (def) e1: " (pretty e1)
                debugM "synthDebug - (def) making a: " (pretty $ Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTySch tyA) y e1)
                debugM "synthDebug - (def) delta1: " (show delta1)
                debugM "synthDebug - (def) delta2: " (show delta2)
                debugM "synthDebug - (def) structurallydecr1: " (show structurallyDecr1)
                debugM "synthDebug - (def) structurallydecr2: " (show structurallyDecr2)

                -- At least one of the sub-components of the application must be structurally decreasing
                if structurallyDecr1 || structurallyDecr2 || not (x `elem` currDef state) then do 
                  -- liftIO $ putStrLn ("making a: " <> (pretty $ Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTySch tyA) y e1))
                  substOut <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
                  return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTySch tyA) y e1, delta2, substOut, bindings1 ++ bindings2, True)
                else none
              _ -> none
          _ -> none
      else none
    _ -> none)
defHelper left (def@(x, (defTySch, appDepth)) : right) gamma omega add@(Additive mode) inDef depth focusPhase grade goal@(Goal goalTySch@(Forall _ binders constraints ty) structure) =
 defHelper (def:left) right gamma omega add inDef depth focusPhase grade goal `try`
 (case defTySch of
    (Forall _ _ _ (FunTy _ _ _)) -> do      

      state <- Synthesiser $ lift $ lift $ get

      -- Only try the def if we haven't hit the def allowed depth 
      if appDepth <= appMax depth then do
        (freshTy, tyVarsFreshD, substFromFreshening, constraints', _) <- conv $ freshPolymorphicInstance InstanceQ False defTySch [] [] 
        case freshTy of 
          (FunTy _ tyA tyB) -> do 
            debugM "synthDebug - (def) in defHelper attempting to use  def: " (pretty def <> " towards goal: " <> pretty goalTySch)
        
            y <- freshIdentifier
            let (gamma', omega') = bindToContext (y, (Linear tyB, AInfo None 0)) (gamma++omega) [] (isLAsync tyB)

            let def' = (x, (defTySch, appDepth+1))

            (e1, delta1, subst1, bindings1, structurallyDecr1) <- synthesiseInner (def':left ++ right) add True depth focusPhase gamma' omega' grade goal

            case lookupAndCutout y delta1 of
              Just (delta1', (Linear _, _)) -> do
                gamma2 <-
                  case mode of
                    NonPruning -> return (omega ++ gamma)
                    Pruning    -> ctxtSubtract (omega ++ gamma) delta1'


                (e2, delta2, subst2, bindings2, structurallyDecr2) <- synthesiseInner (def':left ++ right) add True depth (Focus R Sync) gamma2 [] grade (Goal (Forall nullSpanNoFile binders constraints tyA) structure)

                -- At least one of the sub-components of the application must be structurally decreasing
                if structurallyDecr1 || structurallyDecr2 || not (x `elem` currDef state) then do

                  -- Add the results
                  deltaOut <- maybeToSynthesiser $ ctxtAdd delta1' delta2
                  substOut <- conv $ combineSubstitutions nullSpan subst1 subst2
                  debugM "deltaOut: " (show deltaOut)
                  return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTySch tyA) y e1, deltaOut, substOut, bindings1 ++ bindings2, True)
                else none
              _ -> none
          _ -> none
        else none
    _ -> none)



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
  => Ctxt (TypeScheme, Int)
  -> Ctxt (Assumption, AssumptionInfo)
  -> Ctxt (Assumption, AssumptionInfo)
  -> ResourceScheme PruningScheme
  -> Bool
  -> Depth
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, AssumptionInfo), Substitution, Bindings, Bool)
absHelper defs gamma omega resourceScheme inDef depth focusPhase grade goal@(Goal goalTySch@(Forall _ binders constraints (FunTy name tyA tyB)) structure) = do
  -- Fresh var
  id <- useBinderNameOrFreshen name
  -- Build recursive context depending on focus mode
  let (gamma', omega') = bindToContext (id, (Linear tyA, AInfo NonDecreasing 0)) gamma omega (isLAsync tyA) 

  -- Synthesis body
  debugM "synthDebug" $ "(abs) lambda-binding " ++ pretty [(id, Linear tyA)]
  (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs resourceScheme inDef depth focusPhase gamma' omega' grade (Goal (Forall nullSpanNoFile binders constraints tyB) structure)
  debugM "synthDebug" $ "(abs) made a lambda: " ++ pretty (makeAbs id e goalTySch)
  debugM "synthDebug" $ "(abs) delta: " ++ show delta

  -- Check resource use at the end
  case (resourceScheme, lookupAndCutout id delta) of
    (Additive{}, Just (delta', (Linear _, _))) -> do
      return (makeAbs id e goalTySch, delta', subst, bindings, structurallyDecr)
    (Subtractive, Nothing) ->
      return (makeAbs id e goalTySch, delta, subst, bindings, structurallyDecr)
    _ -> none
absHelper _ _ _ _ _ _ _ _ _ = none


appHelper :: (?globals :: Globals)
  => Ctxt (TypeScheme, Int)
  -> Ctxt (Assumption, AssumptionInfo)
  -> Ctxt (Assumption, AssumptionInfo)
  -> Ctxt (Assumption, AssumptionInfo)
  -> ResourceScheme PruningScheme
  -> Bool
  -> Depth
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, AssumptionInfo), Substitution, Bindings, Bool)
appHelper _ _ _ [] _ _ _ _ _ _ = none
{-
Subtractive

x2 ∉ Δ1
Γ, x2 : B ⊢ C ⇒ t1 ; Δ1
Δ1 ⊢ A ⇒ t2 ; Δ2
------------------------ :: app
Γ, x1 : A → B ⊢ C ⇒ [(x1 t2) / x2] t1 ; Δ2

-}
appHelper defs gamma left (assumption@(x, (ty, (AInfo _ appDepth))) : right) Subtractive inDef depth focusPhase grade goal@(Goal goalTySch@(Forall _ binders constraints _) _) =
  appHelper defs gamma (assumption : left) right Subtractive inDef depth focusPhase grade goal `try`
  (case getAssumptionType ty of
    (FunTy _ tyA tyB) -> do
      -- Only try the app if we haven't hit the app allowed depth 
      if appDepth < (appMax depth) then do

        debugM "synthDebug - (app) trying to use a function " (show assumption ++ " to get goal " ++ pretty goalTySch)

        let omega = left ++ right
        (canUse, leftOver, _) <- useVar assumption omega Subtractive grade
        if canUse 
          then do

            y <- freshIdentifier


            let (gamma', omega') = case lookupAndCutout x leftOver of 
                            Just (omega'', (assTy, AInfo structure _)) -> (gamma ++ [(x, (assTy, AInfo structure (appDepth+1)))], omega'')
                            _ -> (gamma, leftOver)

            -- Extend context (focused) with x2 : B
            let (gamma'', omega'') = bindToContext (y, (Linear tyB, AInfo None 0)) gamma' omega' (isLAsync tyB)



            debugM "gamma'': " (show gamma'')
            debugM "omega'': " (show omega'')
            debugM "goal: " (pretty goalTySch)
            debugM "synthDebug - (app) try to synth the goal " (pretty goalTySch ++ "\n under context of gamma'': " ++ (show gamma'') ++ "\n , omega'': " ++ (show omega''))
            (e1, delta1, subst1, bindings1, structurallyDecr1) <- synthesiseInner defs Subtractive inDef depth focusPhase gamma'' omega'' grade goal
            case lookup y delta1 of
              Nothing -> do
                debugM "synthDebug - (app) try to synth the argument at type "  (pretty tyA)

                -- Synthesise the argument
                (e2, delta2, subst2, bindings2, structurallyDecr2) <- synthesiseInner defs Subtractive inDef depth (Focus R Sync) delta1 [] grade (Goal (Forall nullSpanNoFile binders constraints tyA) NonDecreasing)
                debugM "synthDebug - (app) made an e2: " (pretty $ Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTySch tyA) y e1)
                debugM "delta2: " (show delta2)

                substOut <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
                return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTySch tyA) y e1, delta2, substOut, bindings1 ++ bindings2, structurallyDecr1 || structurallyDecr2)
              _ -> none
        else none
      else none
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
appHelper defs gamma left (assumption@(x, (ty, AInfo structure appDepth)) : right) add@(Additive mode) inDef depth focusPhase grade goal@(Goal goalTySch@(Forall _ binders constraints _) _) =
  appHelper defs gamma (assumption : left) right add inDef depth focusPhase grade goal `try`
  (case getAssumptionType ty of
    (FunTy _ tyA tyB) -> do
      -- Only try the app if we haven't hit the app allowed depth 
      if appDepth <= (appMax depth) then do

        let omega = (left ++ right)
        (canUse, used, _) <- useVar assumption omega add grade

        if canUse
          then do
            -- leftOverOmega <- ctxtSubtract omega used 

            y <- freshIdentifier

            let assumption' = (x, (ty, AInfo structure (appDepth+1)))

            -- Subtract the usage of this function type assumption from the total usage and rebind in gamma
            gammaAfterUse <- ctxtSubtract (assumption':gamma) used

            -- Extend context (focused) with y : B
            let (gamma', omega') = bindToContext (y, (Linear tyB, AInfo None 0)) gammaAfterUse omega (isLAsync tyB)


            -- Synthesise the goal using the result of the application
            (e1, delta1, subst1, bindings1, structurallyDecr1) <- synthesiseInner defs add inDef depth focusPhase gamma' omega' grade goal 

            -- Make sure that `y` appears in the result
            case lookupAndCutout y delta1 of
              Just (delta1',  (Linear _, _)) -> do

                -- Pruning subtraction
                gamma2 <- case mode of
                      NonPruning -> return (omega ++ gammaAfterUse)
                      Pruning    -> ctxtSubtract (omega ++ gammaAfterUse) delta1'

                  -- Synthesise the argument
                (e2, delta2, subst2, bindings2, structurallyDecr2) <- synthesiseInner defs add inDef depth (Focus R Sync) gamma2 [] grade (Goal (Forall nullSpanNoFile binders constraints tyA) NonDecreasing)

                  -- Add the results
                deltaOut <- maybeToSynthesiser $ ctxtAdd used delta1'
                deltaOut' <- maybeToSynthesiser $ ctxtAdd deltaOut delta2

                substOut <- conv $ combineSubstitutions nullSpan subst1 subst2
                return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTySch tyA) y e1, deltaOut', substOut, bindings1 ++ bindings2, structurallyDecr1 || structurallyDecr2)
              _ -> none
        else none
      else none
    _ -> none)


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
  => Ctxt (TypeScheme, Int)
  -> Ctxt (Assumption, AssumptionInfo)
  -> ResourceScheme PruningScheme
  -> Bool
  -> Depth 
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, AssumptionInfo), Substitution, Bindings, Bool)
boxHelper defs gamma resourceScheme inDef depth focusPhase grade (Goal goalTySch@(Forall _ binders constraints (Box g t)) _) = 
  let newGrade = case grade of {Just grade' -> Just $ TyInfix TyOpTimes grade' g ; Nothing -> Nothing}
  in case resourceScheme of
      Additive{} -> do
        (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs resourceScheme inDef depth focusPhase gamma [] newGrade (Goal (Forall nullSpanNoFile binders constraints t) NonDecreasing) 
        case hasLinearVars delta of 
          False -> do deltaOut <- case newGrade of {Just _ -> return delta ; Nothing -> ctxtMultByCoeffect g delta}
                      return (makeBox goalTySch e, deltaOut, subst, bindings, structurallyDecr)
          True  -> none
      Subtractive -> do
        (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs resourceScheme inDef depth focusPhase gamma [] newGrade (Goal (Forall nullSpanNoFile binders constraints t) NonDecreasing)
        deltaOut <- case newGrade of
            Just _ -> return delta
            Nothing -> do
              used <- ctxtSubtract gamma delta
              -- Compute what was used to synth e
              delta' <- ctxtMultByCoeffect g used
              ctxtSubtract gamma delta'
        res <- solve
        boolToSynthesiser res (makeBox goalTySch e, deltaOut, subst, bindings, structurallyDecr)
  
  where 

    hasLinearVars [] = False
    hasLinearVars ((x, (Linear _, _)):xs) = True
    hasLinearVars ((x, (_, _)):xs) = hasLinearVars xs

boxHelper _ _ _ _ _ _ _ _ = none


unboxHelper :: (?globals :: Globals)
  => Ctxt (TypeScheme, Int)
  -> Ctxt (Assumption, AssumptionInfo)
  -> Ctxt (Assumption, AssumptionInfo)
  -> Ctxt (Assumption, AssumptionInfo)
  -> ResourceScheme PruningScheme
  -> Bool
  -> Depth  
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, AssumptionInfo), Substitution, Bindings, Bool)
unboxHelper _ _ _ [] _ _ _ _ _ _ = none
{-
Subtractive
0 <= s
Γ, x2 : [A] r ⊢ B ⇒ e ; Δ, x2 : [A] s
-------------------------------------------- :: unbox
Γ, x1 : [] r A ⊢ B ⇒ let [x2] = x1 in e; Δ

-}
unboxHelper defs gamma left (assumption@(x, (ty, info)) : right) Subtractive inDef depth focusPhase grade goal@(Goal goalTySch _) =
  unboxHelper defs gamma (assumption : left) right Subtractive inDef depth focusPhase grade goal `try`
    (case ty of
      Linear (Box grade_r tyA) -> do

        debugM "synthDebug" $ "Trying to unbox " ++ show assumption

        let omega = left ++ right
        (canUse, leftOver, _) <- useVar assumption omega Subtractive grade
        if canUse then do
          ---
          y <- freshIdentifier
          let (gamma', omega') = bindToContext (y, (Discharged tyA grade_r, info)) gamma leftOver (isLAsync tyA)
          debugM "synthDebug" $ "Inside unboxing try to synth for " ++ pretty goalTySch ++ " under " ++ pretty [(y, Discharged tyA grade_r)]

          (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs Subtractive inDef depth focusPhase gamma' omega' grade goal
          ---
          case lookupAndCutout y delta of
            Just (delta', (Discharged _ grade_s, _)) -> do
              -- Check that: 0 <= s
              (kind, _, _) <- conv $ synthKind nullSpan grade_s
              s <- conv get
              modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade_s kind) (predicateContext s)
              res <- solve

              -- If we succeed, create the let binding
              boolToSynthesiser res (makeUnbox y x goalTySch (Box grade_r tyA) tyA e, delta', subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr)
            _ -> none
        else none
      Discharged (Box grade_r tyA) grade_s -> do
        debugM "synthDebug - (unbox - double) trying a double unboxing with "  (show grade_r)
      
       -- _ <- error "stoppp"
        let omega = left ++ right
        (canUse, _, _) <- useVar assumption [] Subtractive grade 
        if canUse then do 
          y <- freshIdentifier
          let (gamma', omega') = bindToContext (y, (Discharged tyA (TyInfix TyOpTimes grade_r grade_s), info)) gamma omega (isLAsync tyA) 
          (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs Subtractive inDef depth focusPhase gamma' omega' grade goal 
          case lookupAndCutout y delta of
            Just (delta', (Discharged _ grade_s', _)) ->  do 
              (kind, _, _) <- conv $ synthKind nullSpan grade_s'
              r' <- freshIdentifier 
              conv $ existentialTopLevel r' kind
              s <- conv get
              modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyInfix TyOpTimes (TyVar r') grade_s) grade_s' kind) (predicateContext s)
              res <- solve 
              debugM "synthDebug - (unbox - double) term: " (pretty $ makeUnbox y x goalTySch (Box grade_r tyA) tyA e)
              boolToSynthesiser res (makeUnbox y x goalTySch (Box grade_r tyA) tyA e, replace delta' x (Discharged (Box grade_r tyA) (TyVar r'), info), subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr)
            _ -> none
        else none
      _ -> none)
{-
Additive

s <= r
Γ, x2 : [A] r ⊢ B ⇒ t ; D, x2 : [A] s
--------------------------------------------------------- :: unbox
Γ, x1 : [] r A ⊢ B ⇒ let [x2] = x1 in t ; Δ, x1 : [] r A

-}
unboxHelper defs gamma left (assumption@(x, (ty, info)) : right) add@(Additive{}) inDef depth focusPhase grade goal@(Goal goalTySch _) =
  unboxHelper defs gamma (assumption : left) right add inDef depth focusPhase grade goal `try`
   (case ty of
     (Linear (Box grade_r tyA)) -> do
       let omega = left ++ right
       (canUse, used, t) <- useVar assumption omega add grade
       if canUse
          then do
            y <- freshIdentifier
            -- omega1 <- ctxtSubtract omega omega'
            let (gamma', omega') = bindToContext (y, (Discharged tyA grade_r, info)) gamma omega (isLAsync tyA)

            -- Synthesise the body of a `let` unboxing
            (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs add inDef depth focusPhase gamma' omega' grade goal

            -- Add usage at the binder to the usage in the body
            delta' <- maybeToSynthesiser $ ctxtAdd used delta

            s <- conv get

            -- _ <- error "stop"

            case lookupAndCutout y delta' of
              Just (delta'', (Discharged _ grade_s, _)) -> do
                (kind, _, _) <- conv $ synthKind nullSpan grade_r
                modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile grade_s grade_r kind) (predicateContext s)
                res <- solve
                boolToSynthesiser res (makeUnbox y x goalTySch tyA (Box grade_r tyA) e,  delta'', subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr) 
              _ -> do
                (kind, _, _) <- conv $ synthKind nullSpan grade_r
                modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade_r kind) (predicateContext s)
                res <- solve
                boolToSynthesiser res (makeUnbox y x goalTySch tyA (Box grade_r tyA) e,  delta', subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr) 
          else none
     (Discharged (Box grade_r tyA) grade_s) -> do
        let omega = left ++ right
        (canUse, _, _) <- useVar assumption [] add grade
        if canUse then do
          y <- freshIdentifier
          let (gamma', omega') = bindToContext (y, (Discharged tyA (TyInfix TyOpTimes grade_r grade_s), info)) gamma omega (isLAsync tyA)
          (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs add inDef depth focusPhase gamma' omega' grade goal 

          s <- conv get

          case lookupAndCutout y delta of
            Just (delta', (Discharged _ grade_s', _)) ->  do
              (kind, _, _) <- conv $ synthKind nullSpan grade_s'
              r' <- freshIdentifier 
              conv $ existentialTopLevel r' kind

              modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyInfix TyOpTimes (TyVar r') grade_s) (TyInfix TyOpTimes grade_r grade_s) kind) (predicateContext s)
              modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyInfix TyOpTimes (TyVar r') grade_s) grade_s' kind) (predicateContext s)

              res <- solve

              boolToSynthesiser res (makeUnbox y x goalTySch (Box grade_r tyA) tyA e, replace delta x (Discharged (Box grade_r tyA) (TyVar r'), info), subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr)
            _ -> do
                (kind, _, _) <- conv $ synthKind nullSpan grade_r
                modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) (TyInfix TyOpTimes grade_r grade_s) kind) (predicateContext s)
                res <- solve
                boolToSynthesiser res (makeUnbox y x goalTySch (Box grade_r tyA) tyA e, delta, subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr)
        else none

     _ -> none)



constrIntroHelper :: (?globals :: Globals)
  => Ctxt (TypeScheme, Int)
  -> Ctxt (Assumption, AssumptionInfo)
  -> ResourceScheme PruningScheme
  -> Bool
  -> Depth 
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, AssumptionInfo), Substitution, Bindings, Bool)
constrIntroHelper defs gamma resourceScheme False depth focusPhase grade goal@(Goal goalTySch@(Forall s binders constraints tyA) structure) =
  case (isADTorGADT tyA) of
    Just name -> do
      if (iCurr depth) <= (iMax depth) || structure /= Decreasing then do


        debugM "synthDebug - entered constrIntroHelper with goal: " (show goal)
        debugM "synthDebug - entered constrIntroHelper with gamma: " (show gamma)
        state <- Synthesiser $ lift $ lift $ get

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
                let delta = case resourceScheme of {Additive{} -> []; Subtractive{} -> gamma}
                return (Just $ makeNullaryConstructor conName, delta, conSubst, [], False) 
              Just conArgs -> do 
                args <- conv $ mapM (\s -> do 
                  s' <- substitute substFromFreshening s
                  s'' <- substitute specSubst s'
                  return (s'', boolToStructure $ isDecreasing adtName [s])) conArgs
                (exprs, delta, subst, bindings, structurallyDecr) <- synthConArgs adtName (constructors state) defs args conBinders conConstraints conSubst
                return (Just $ makeConstr exprs conName conTy, delta, subst, bindings, structurallyDecr) 
              Nothing -> none
          _ -> none

    constrArgs :: Type -> Maybe [Type]
    constrArgs (TyCon _) = Just []
    constrArgs (TyApp _ _) = Just []
    constrArgs (FunTy _ e1 e2) = do
      res <- constrArgs e2
      return $ e1 : res
    constrArgs _ = Nothing

    -- Traverse the argument types to the constructor and synthesise a term for each one
    synthConArgs tyAName consGlobal defs [(argTyA, isDecr)] conBinders conConstraints conSubst = do
      (expr, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs resourceScheme False (if isDecr == Decreasing then depth { iCurr = (iCurr depth) + 1 } else depth) (Focus R Async) gamma [] grade (Goal (Forall s conBinders conConstraints argTyA) isDecr)
      subst' <- conv $ combineSubstitutions nullSpanNoFile conSubst subst
      debugM "constrIntro with goal: " (pretty goalTySch <> " made a " <> pretty expr <> " for arg " <> pretty argTyA)
      return ([(expr, argTyA)], delta, subst', bindings, structurallyDecr)
    synthConArgs tyAName consGlobal defs ((argTyA, isDecr):args) conBinders conConstraints conSubst = do
      (exprs, deltas, substs, bindings, structurallyDecr) <- synthConArgs tyAName consGlobal defs args conBinders conConstraints conSubst
      substs' <- conv $ combineSubstitutions nullSpanNoFile conSubst substs
      gamma' <- case resourceScheme of
            Additive NonPruning -> return gamma
            Additive Pruning -> ctxtSubtract gamma deltas -- Pruning
            Subtractive -> return deltas
      (expr, delta, subst, bindings', structurallyDecr') <- synthesiseInner defs resourceScheme False (if isDecr == Decreasing then depth { iCurr = (iCurr depth) + 1 } else depth) (Focus R Async) gamma' [] grade (Goal (Forall s conBinders conConstraints argTyA) isDecr)
      subst'' <- conv $ combineSubstitutions nullSpanNoFile subst substs'
      delta' <- case resourceScheme of
            Additive{} -> maybeToSynthesiser $ ctxtAdd deltas delta
            Subtractive -> return delta
      return ((expr, argTyA):exprs, delta', subst'', bindings ++ bindings', structurallyDecr || structurallyDecr')
    synthConArgs _ _ _ _ _ _ _ = none

    boolToStructure False = NonDecreasing
    boolToStructure True  = Decreasing

constrIntroHelper _ _ _ _ _ _ _ _ = none

{- 

Constructor elimination
=======================


-}
constrElimHelper :: (?globals :: Globals)
  => Ctxt (TypeScheme, Int)
  -> Ctxt (Assumption, AssumptionInfo)
  -> Ctxt (Assumption, AssumptionInfo)
  -> Ctxt (Assumption, AssumptionInfo)
  -> ResourceScheme PruningScheme
  -> Bool 
  -> Depth
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, AssumptionInfo), Substitution, Bindings, Bool)
constrElimHelper _ _ _ [] _ _ _ _ _ _ = none
constrElimHelper defs gamma left (assumption@(x, (tyA, (AInfo structure eDepth))):right) mode False depth focusPhase grade goal@(Goal goalTySch@(Forall _ _ _ tyB) _) =
  constrElimHelper defs gamma (assumption:left) right mode False depth focusPhase grade goal `try` do
    state <- Synthesiser $ lift $ lift $ get
    if eDepth <= eMax depth  || structure /= Decreasing then do

      debugM "synthDebug in constrElimHelper with assumption: " (show assumption <> " and goal " <> show tyB)
      let omega = (left ++ right)
      (canUse, usageOut, _) <- useVar assumption omega mode grade

      let (assumptionTy, assumptionGrade) = case tyA of
            Linear tyA' -> (tyA', Nothing)
            Discharged tyA' grade_r -> (tyA', Just grade_r)

      if canUse then
        case isADTorGADT assumptionTy of
          Just name -> do
       
            let (recursiveCons, nonRecursiveCons) = relevantConstructors name (constructors state)
            let sortedCons = sortBy compareArity nonRecursiveCons ++ sortBy compareArity recursiveCons

            (patterns, delta, resSubst, resBindings, structurallyDecr, _) <- foldM (\ (exprs, deltas, substs, bindings, structurallyDecr, index) (conId, (conTySch@(Forall s binders constraints conTy), conSubst)) -> do

              let pred = newImplication [] (predicateContext cs)

              debugM "compiletoSBV ELIM (check constructor)" $ pretty conId
              result <- checkConstructor True conTySch assumptionTy conSubst

              let predSucceeded = moveToConsequent pred

              case (result, predSucceeded) of 
                ((True, specTy, conTyArgs, conSubst', _), Right pred'@(ImplConsequent ctxt p path)) -> do

                  modifyPred pred'

                  -- Calculate assumptions
                  assumptions <- mapM (\ arg -> do
                    y <- freshIdentifier 
                    arg' <- conv $ substitute conSubst' arg
                    let assumptionType = case assumptionGrade of {Nothing -> Linear arg'; Just grade_r -> Discharged arg' grade_r}
                    let assumption = if isRecursiveCon name (y, (Forall nullSpanNoFile binders constraints arg, [])) then (y, (assumptionType, AInfo Decreasing (eDepth+1))) else (y, (assumptionType, AInfo NonDecreasing eDepth))
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
                          Just (usageOut', (ty', AInfo structure' _)) -> return (gamma ++ [(x, (ty', AInfo structure' (eDepth+1)))], usageOut')
                          _ -> return (gamma, usageOut)                  
                  
                  -- Required for focusing with recursive data structures. If we have hit the depth limit but still have other vars in omega 
                  -- that cannot be decomposed we need to move them into gamma

                  let (gamma'', omega'', unboxed) = bindAssumptions (eDepth + 1 > maxDepth depth) [] assumptions gamma' omega'

                  (expr, delta, subst, bindings, structurallyDecr') <- synthesiseInner defs mode False depth focusPhase gamma'' omega'' grade goal 
                  debugM "expr; " (pretty expr)
                
                  delta' <- checkAssumptions (x, assumptionTy) mode delta assumptions unboxed
                  -- _ <- error "stop"
                  
                  case transformPattern bindings assumptionTy (gamma'' ++ omega'') constrElimPattern unboxed of
                    Just (pattern, bindings') ->
                      let mergeOp = case mode of Additive{} -> TyInfix TyOpJoin ; _ -> TyInfix TyOpMeet in do
                        returnDelta <- if index == 0 then return delta' else ctxtMerge mergeOp deltas delta' 
                        modifyPred $ moveToNewConjunct (predicateContext cs)
                        returnSubst <- conv $ combineSubstitutions nullSpanNoFile subst substs
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
                return (makeCase assumptionTy x patterns tyB assumptionGrade, finDelta, resSubst, resBindings, structurallyDecr)
              _ -> none
          _ -> none   
      else none
    else none

  where 

  makePattern :: Id ->  [Id] -> Maybe Type -> Pattern ()
  makePattern conId vars _ = PConstr nullSpanNoFile () False conId (map (PVar nullSpanNoFile () False) vars)
    
  bindAssumptions :: Bool
    -> Ctxt (Assumption, AssumptionInfo)
    -> Ctxt (Assumption, AssumptionInfo)
    -> Ctxt (Assumption, AssumptionInfo)
    -> Ctxt (Assumption, AssumptionInfo)
    -> (Ctxt (Assumption, AssumptionInfo), Ctxt (Assumption, AssumptionInfo), Ctxt (Assumption, AssumptionInfo))
  bindAssumptions depthReached unboxed [] gamma omega = (gamma, omega, unboxed)

  bindAssumptions depthReached unboxed (assumption@(id, (Linear t, AInfo structure depth)):assmps) gamma omega =
    let gammaOrOmega = if depthReached && (structure == Decreasing) then False else isLAsync t in
    let (gamma', omega') = bindToContext assumption gamma omega gammaOrOmega in
    bindAssumptions depthReached unboxed assmps gamma' omega' 

  bindAssumptions depthReached unboxed (assumption@(id, (Discharged (Box t grade) grade', AInfo structure depth)):assmps) gamma omega =
    let gammaOrOmega = if depthReached && (structure == Decreasing) then False else isLAsync t in
    let (gamma', omega') = bindToContext (id, (Discharged t (TyInfix TyOpTimes grade grade'), AInfo structure depth)) gamma omega gammaOrOmega in
    bindAssumptions depthReached ((id, (Discharged t (TyInfix TyOpTimes grade grade'), AInfo structure depth)):unboxed) assmps gamma' omega' 

  bindAssumptions depthReached unboxed (assumption@(id, (Discharged t _, AInfo structure depth)):assmps) gamma omega =
    let gammaOrOmega = if depthReached && (structure == Decreasing) then False else isLAsync t in
    let (gamma', omega') = bindToContext assumption gamma omega gammaOrOmega in
    bindAssumptions depthReached unboxed assmps gamma' omega' 


  checkAssumptions :: (?globals::Globals) 
    => (Id, Type)
    -> ResourceScheme PruningScheme
    -> [(Id, (Assumption, AssumptionInfo))]
    -> [(Id, (Assumption, AssumptionInfo))]
    -> Ctxt (Assumption, AssumptionInfo) -> Synthesiser [(Id, (Assumption, AssumptionInfo))]
  checkAssumptions _ mode del [] _ = return del
  checkAssumptions x sub@Subtractive{} del ((id, (Linear t, info)):assmps) unboxed =
    case lookup id del of
      Nothing -> checkAssumptions x sub del assmps unboxed
      _ -> none
  checkAssumptions (x, t') sub@Subtractive{} del ((id, (Discharged t g, info)):assmps) unboxed = do
    s <- getSynthState
    case lookupAndCutout id del of
      Just (del', (Discharged _ g', info)) ->
        case lookup id unboxed of
          Just (Discharged _ g'', info) -> do
            del'' <- checkAssumptions (x, t') sub del' assmps unboxed
            (kind, _, _) <- conv $ synthKind nullSpan g'
            modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) g' kind) (predicateContext s)
            res <- solve
            if res then do
              ctxtMerge (TyInfix TyOpMeet) [(x, (Discharged t' g, info))] del''
            else none
          _ -> do
            del'' <- checkAssumptions (x, t') sub del' assmps unboxed
            (kind, _, _) <- conv $ synthKind nullSpan g'
            modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) g' kind) (predicateContext s)
            res <- solve
            if res then
              ctxtMerge (TyInfix TyOpMeet) [(x, (Discharged t' g', info))] del''
            else none
      _ -> none


  -- Additive
  checkAssumptions x add@Additive{} del ((id, (Linear t, info)):assmps) unboxed =
    case lookupAndCutout id del of
      Just (del', _) ->
        checkAssumptions x add del' assmps unboxed
      _ -> none
  checkAssumptions (x, t') add@Additive{} del ((id, (Discharged t g, info)):assmps) unboxed = do
        s <- conv get
        case lookupAndCutout id del of
          Just (del', (Discharged _ g', info)) ->
            case lookup id unboxed of
              Just (Discharged _ g'', info) -> do
                del'' <- checkAssumptions (x, t') add del' assmps unboxed
                (kind, _, _) <- conv $ synthKind nullSpan g'
                modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile g' g'' kind) (predicateContext s)
                res <- solve
                if res then do
                  ctxtMerge (TyInfix TyOpJoin) [(x, (Discharged t' g, info))] del''
                else none
              _ -> (do
                del'' <- checkAssumptions (x, t') add del' assmps unboxed
                (kind, _, _) <- conv $ synthKind nullSpan g
                modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile g' g kind) (predicateContext s)
                res <- solve
                if res then 
                  ctxtMerge (TyInfix TyOpJoin) [(x, (Discharged t' g', info))] del''
                else none)
          _ -> do
            (kind, _, _) <- conv $ synthKind nullSpan g
            modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) g kind) (predicateContext s)
            res <- solve
            if res then checkAssumptions (x, t') add del assmps unboxed else none


  -- Construct a typed pattern from an untyped one from the context
  transformPattern :: 
       Ctxt (Id, Type)
    -> Type 
    -> [(Id, (Assumption, AssumptionInfo))] 
    -> Pattern () 
    -> Ctxt (Assumption, AssumptionInfo) 
    -> Maybe (Pattern Type, Ctxt (Id, Type))
  transformPattern bindings adt ctxt (PConstr s () b id pats) unboxed = do
    (pats', bindings') <- transformPatterns bindings adt ctxt pats unboxed
    Just (PConstr s adt b id pats', bindings)
  transformPattern bindings adt ctxt (PVar s () b name) unboxed =
    let (pat, name', bindings') = case lookup name unboxed of
          Just (Discharged ty _, info) -> (PBox s ty False, name, bindings)
          _ -> (id, name, bindings)
    in
    case lookup name ctxt of
       Just (Linear t, info) -> Just (pat $ PVar s t b name', bindings')
       Just (Discharged t c, info) -> Just (pat $ PVar s t b name', bindings')
       Nothing -> Nothing
  transformPattern bindings adt ctxt (PBox s () b p) unboxed = do
    (pat', bindings') <- transformPattern bindings adt ctxt p unboxed
    Just (PBox s adt b pat', bindings')
  transformPattern _ _ _ _ _ = Nothing


  transformPatterns :: 
       Ctxt (Id, Type) 
    -> Type 
    -> [(Id, (Assumption, AssumptionInfo))] 
    -> [Pattern ()]
    -> Ctxt (Assumption, AssumptionInfo) 
    -> Maybe ([Pattern Type], Ctxt (Id, Type))
  transformPatterns bindings adt ctxt [] unboxed = Just ([], bindings)
  transformPatterns bindings adt ctxt (p:ps) unboxed = do
    (pat, bindings') <- transformPattern bindings adt ctxt p unboxed
    (res, bindingsFinal) <- transformPatterns bindings' adt ctxt ps unboxed
    return (pat:res, bindingsFinal)

constrElimHelper _ _ _ _ _ _ _ _ _ _ = none



synthesiseInner :: (?globals :: Globals)
           => Ctxt (TypeScheme, Int)
           -> ResourceScheme PruningScheme       
           -> Bool
           -> Depth 
           -> FocusPhase     
           -> Ctxt (Assumption, AssumptionInfo)    -- (unfocused) free variables
           -> Ctxt (Assumption, AssumptionInfo)    
           -> Maybe Type
           -> Goal          
           -> Synthesiser (Expr () Type, Ctxt (Assumption, AssumptionInfo), Substitution, Bindings, Bool)
synthesiseInner defs resourceScheme inDef depth focusPhase gamma omega grade goal@(Goal goalTySch@(Forall _ _ _ ty) info) = do

  currentTime    <- liftIO $ Clock.getTime Clock.Monotonic
  state <- Synthesiser $ lift $ lift $ lift get
  Synthesiser $ lift $ lift $ lift $ modify (\state ->
            state {
                --  elimDepthReached  = if not $ elimDepthReached state  then eCurr depth  >= eMax depth else True
                introDepthReached = if not $ introDepthReached state then iCurr depth >= iMax depth else True
              -- ,  appDepthReached = if not $ appDepthReached state then appCurr depth >= appMax depth else True
                  })

  debugM "synthDebug - synthesiseInner with goal: " (show goal)
  debugM "synthDebug - synthesiseInner with gamma: " (show gamma)
  debugM "synthDebug - synthesiseInner with omega: " (show omega)
  debugM "synthDebug - synthesiseInner with focusPhase: " (show focusPhase)

  debugM "synthDebug - synthesiseInner with current e max: " (show $ eMax depth)
  debugM "synthDebug - synthesiseInner with current i depth: " (show $ iCurr depth)
  debugM "synthDebug - synthesiseInner with current i max: " (show $ iMax depth)
  debugM "synthDebug - synthesiseInner with current app max: " (show $ appMax depth)

  debugM "synthDebug - synthesiseInner with elim depth reached: " (show $ elimDepthReached state)
  debugM "synthDebug - synthesiseInner with intro depth reached: " (show $ introDepthReached state)
  debugM "synthDebug - synthesiseInner with app depth reached: " (show $ appDepthReached state)

  case (focusPhase, omega) of 

    (Focus R Async, _) -> do
      varHelper [] [] (gamma ++ omega) resourceScheme grade goal
      `try`
      absHelper defs gamma omega resourceScheme inDef depth (Focus R Async) grade goal
      `try`
      rightAsyncTrans ty
    (Focus L Async, (x:xs)) -> do 
      varHelper [] [] (gamma ++ omega) resourceScheme grade goal
      `try`
      unboxHelper defs gamma [] omega resourceScheme inDef depth (Focus L Async) grade goal
      `try`
      constrElimHelper defs gamma [] omega resourceScheme inDef depth (Focus L Async) grade goal
    (Focus L Async, []) -> do
      focus gamma (isRSync ty) 
    (Focus R Sync, []) ->
      case not $ isRSync ty of 
        True -> 
          synthesiseInner defs resourceScheme inDef depth (Focus R Async) gamma [] grade goal
        _ -> 
          varHelper [] [] gamma resourceScheme grade goal
          `try`
          constrIntroHelper defs gamma resourceScheme inDef depth (Focus R Sync) grade goal
          `try`
          boxHelper defs gamma resourceScheme inDef depth (Focus R Sync) grade goal
    (Focus L Sync, assumption@(x, (tyA, _)):[]) -> 
      let tyA' = getAssumptionType tyA in
      case (not $ isLSync tyA') && (not $ isAtomic tyA') of 
        True -> synthesiseInner defs resourceScheme inDef depth (Focus L Async) gamma [assumption] grade goal
        _ -> do
          varHelper gamma [] omega resourceScheme grade goal
          `try`
          defHelper [] defs gamma omega resourceScheme inDef depth (Focus L Sync) grade goal
          `try`
          appHelper defs gamma [] omega resourceScheme inDef depth (Focus L Sync) grade goal
    (Focus L Sync, []) -> do
        synthesiseInner defs resourceScheme inDef depth (Focus R Async) gamma [] grade goal


  where 

    rightAsyncTrans (FunTy{}) = none 
    rightAsyncTrans _ = synthesiseInner defs resourceScheme inDef depth (Focus L Async) gamma omega grade goal

    focus gamma True =  
      synthesiseInner defs resourceScheme inDef depth (Focus R Sync) gamma [] grade goal
      `try`
      focusLeft [] gamma 
    focus gamma False = focusLeft [] gamma

    focusLeft _ [] = none
    focusLeft left (assumption:right) = 
      focusLeft (assumption : left) right
      `try`
      synthesiseInner defs resourceScheme inDef depth (Focus L Sync) (left ++ right) [assumption] grade goal
    
    -- appLimsReached defs [] max = defLimsReached defs max
    -- appLimsReached defs ((x, (_, AInfo _ depth)):xs) max =  if depth > max then appLimsReached defs xs max else False

    -- defLimsReached [] _ = True
    -- defLimsReached ((x, (_, depth)):xs) max = if depth > max then defLimsReached defs max else False




synthesise :: (?globals :: Globals)
           => Ctxt (TypeScheme, Int)
           -> ResourceScheme PruningScheme    -- whether the synthesis is in additive mode or not
           -> Ctxt (Assumption, AssumptionInfo)    -- (unfocused) free variables
           -> Ctxt (Assumption, AssumptionInfo)    -- focused variables
           -> Depth 
           -> Maybe Type
           -> Goal           -- type from which to synthesise
           -> Synthesiser (Expr () Type, Ctxt (Assumption, AssumptionInfo), Substitution)
synthesise defs resourceScheme gamma omega depth grade goal = do


  st' <- get
  relevantConstructors <- do 
      let snd3 (a, b, c) = b
          tripleToTup (a, b, c) = (a, b)
      st <- get
      let pats = map (second snd3) (typeConstructors st)
      mapM (\ (a, b) -> do
          dc <- conv $ mapM (lookupDataConstructor nullSpanNoFile) b
          let sd = zip (fromJust $ lookup a pats) (catMaybes dc)
          return (a, ctxtMap tripleToTup sd)) pats

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

  result@(expr, ctxt, subst, bindings, _) <- synthesiseInner defs resourceScheme False depth (Focus R Async) gamma omega grade goal

  case resourceScheme of
    Subtractive -> do
      -- All linear variables should be gone
      -- and all graded should approximate 0
      consumed <- mapM (\(id, (a, s)) ->
                    case a of
                      Linear{} -> return False;
                      Discharged _ grade -> do
                        (kind, _, _) <-  conv $ synthKind nullSpan grade
                        s <- conv get 
                        modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade kind) (predicateContext s)
                        solve) ctxt
      if and consumed
        then return (expr, ctxt, subst)
        else none

    -- All linear variables should have been used
    -- and all graded assumptions should have usages which approximate their original assumption
    Additive{} -> do
      consumed <- mapM (\(id, (a, s)) ->
                    case lookup id ctxt of
                      Just (Linear{}, _) -> return True;
                      Just (Discharged _ gradeUsed, _) ->
                        case a of
                          Discharged _ gradeSpec -> do
                            (kind, _, _) <- conv $ synthKind nullSpan gradeUsed
                            s <- conv get
                            modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile gradeUsed gradeSpec kind) (predicateContext s)
                            solve
                          _ -> return False
                      Nothing ->
                        case a of
                          Discharged _ gradeSpec -> do
                            (kind, _, _) <- conv $ synthKind nullSpan gradeSpec
                            s <- conv get
                            modifyPred $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) gradeSpec kind) (predicateContext s)
                            solve
                          _ -> return False) (gamma ++ omega)
      if and consumed
        then return (expr, ctxt, subst)
        else none


-- Run from the checker
synthesiseProgram :: (?globals :: Globals)
           => [Hint]
           -> Ctxt TypeScheme      
           -> Maybe Id 
           -> ResourceScheme PruningScheme       -- whether the synthesis is in additive mode or not
           -> Ctxt Assumption    -- (unfocused) free variables
           -> TypeScheme           -- type from which to synthesise
           -> CheckerState
           -> IO [Expr () Type]
synthesiseProgram hints defs currentDef resourceScheme gamma goalTy checkerState = do

  start <- liftIO $ Clock.getTime Clock.Monotonic

  let initialState = SynthesisData {
                         smtCallsCount= 0 
                      ,  smtTime= 0 
                      ,  proverTime= 0 
                      ,  theoremSizeTotal= 0 
                      ,  pathsExplored= 0 
                      ,  startTime=start 
                      ,  constructors=[] 
                      ,  currDef = (maybeToList currentDef)
                      ,  elimDepthReached = False
                      ,  introDepthReached = False
                      ,  appDepthReached = False
                      ,  predicateContext = Top
                      }



  let gradeOnRule = (fromMaybe False (globalsGradeOnRule ?globals) || HGradeOnRule `elem` hints)
  let initialGrade = if gradeOnRule then Just (TyGrade Nothing 1)  else Nothing

  let timeoutLim = fromMaybe 1000 $ hasTimeoutHint hints
  let timeoutLim' = if HSynNoTimeout `elem` hints then negate timeoutLim else (timeoutLim * 1000)
  let index = fromMaybe 1 $ hasSynthIndex hints

  let (hintELim, hintILim) = case (hasElimHint hints, hasIntroHint hints) of 
            (Just e, Just i)   -> (e, i)
            (Just e, Nothing)  -> (e, 1)
            (Nothing, Just i)  -> (1, i)
            (Nothing, Nothing) -> (1, 1)
        
  let gamma' = map (\(v, a) -> (v, (a, AInfo None 0))) gamma

  -- Only use the defs that are specified in the hint (or all defs if this hint is specified)
  let defs' = if HUseAllDefs `elem` hints then map (\(x, ty) -> (x, (ty, 0))) defs 
              else case hasDefsHint hints of 
                        Just ids -> foldr (\(id, ty) acc -> if id `elem` ids then (id, (ty, 0)):acc else acc) [] defs
                        Nothing -> if HUseRec `elem` hints then foldr (\(id, ty) acc -> if id `elem` (maybeToList currentDef) then (id, (ty, 0)):acc else acc) [] defs else []



  result <- liftIO $ System.Timeout.timeout timeoutLim' $ loop (hintELim, hintILim) index defs' initialGrade gamma' 0 initialState
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
      return results
    _ -> do
      end    <- liftIO $ Clock.getTime Clock.Monotonic
      printInfo $ "No programs synthesised - Timeout after: " <> (show timeoutLim  <> "ms")
      return []
  return fin
  


  where

      loop (eHintMax, iHintMax) index defs grade gamma level agg = do 
        let (elimMax, introMax) = (if level < eHintMax then level else eHintMax, if level < iHintMax then level else iHintMax)

--      Diagonal search
--      let lims = runOmega $ liftM3 (,,) (each [0..elimMax]) (each [0..introMax]) (each [0..level])

--      Rectilinear search
        let norm (x,y,z) = sqrt (fromIntegral x^2+fromIntegral y^2+fromIntegral z^2)
        let mergeByNorm = Ordered.mergeAllBy (comparing norm)
        let lims = mergeByNorm (map mergeByNorm [[[(x,y,z)| x <- [0..elimMax]] | y <- [0..introMax]] | z <- [0..level]])


        pRes <- foldM (\acc (elim, intro, app) -> 
          case acc of 
            (Just res, agg') -> return (Just res, agg')
            (Nothing, agg')  -> do 
              putStrLn $  "elim: " <> (show elim) <> " intro: " <> (show intro) <> " app: " <> (show app) <> " level: " <> (show level)  
              let synRes = synthesise defs resourceScheme gamma [] (Depth elim 0 intro level) grade (Goal goalTy NonDecreasing)
              (res, agg'') <- runStateT (runSynthesiser index synRes checkerState) (resetState agg')
              if (not $ solved res) && (depthReached agg'') then return (Nothing, agg'') else return (Just res, agg'')
          ) (Nothing, agg) lims
        case pRes of 
          (Just finRes, finAgg) -> return (finRes, finAgg)
          (Nothing, finAgg) -> loop (eHintMax, iHintMax) index defs grade gamma (level+1) finAgg 
 

      depthReached st = elimDepthReached st || introDepthReached st || appDepthReached st 
      solved res = case res of ((Right (expr, _, _), _):_) -> True ; _ -> False
      resetState st = st { elimDepthReached = False, introDepthReached = False, appDepthReached = False}



      hasTimeoutHint ((HSynTimeout x):hints) = Just x
      hasTimeoutHint (_:hints) = hasTimeoutHint hints
      hasTimeoutHint [] = Nothing

      hasSynthIndex ((HSynIndex x):hints) = Just x
      hasSynthIndex (_:hints) = hasSynthIndex hints
      hasSynthIndex [] = Nothing

      hasDefsHint ((HUseDefs ids):hints) = Just ids
      hasDefsHint (_:hints) = hasDefsHint hints
      hasDefsHint [] = Nothing

      hasElimHint ((HMaxElim x):hints) = Just x
      hasElimHint ((HNoMaxElim):hints) = Just 9999 
      hasElimHint (_:hints) = hasElimHint hints
      hasElimHint [] = Nothing

      hasIntroHint ((HMaxIntro x):hints) = Just x
      hasIntroHint ((HNoMaxIntro):hints) = Just 9999 
      hasIntroHint (_:hints) = hasIntroHint hints
      hasIntroHint [] = Nothing

      fst3 (x, y, z) = x

      
        
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