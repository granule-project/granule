{-# LANGUAGE ImplicitParams #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}


{-# options_ghc -fno-warn-incomplete-uni-patterns #-}
module Language.Granule.Synthesis.Synth where

import qualified Data.Map as M

import Data.List (sortBy,nub)

import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
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

import Language.Granule.Utils
import Data.Maybe (fromJust, catMaybes, fromMaybe, maybeToList)
import Control.Arrow (second)
import Control.Monad.Omega
import System.Clock (TimeSpec)



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

data Depth = Depth 
  {
    eCurr   :: Int  
  , eMax    :: Int  -- Maximum number of eliminations (of recursive data structures) allowed
  , iCurr   :: Int 
  , iMax    :: Int  -- Maximum number of introductions (of recursive data structures) allowed
  , appCurr :: Int
  , appMax  :: Int  -- Maximum number of nested applications allowed
  , synCurr :: Int 
  , synMax  :: Int  -- Maxmimum depth of focusing (used to terminate endless chains of focusing)
  }
  deriving (Show, Eq)

data Structure = None | NonDecreasing | Decreasing
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
  let pred = Conj $ predicateStack cs
  debugM "synthDebug" ("SMT on pred = " ++ pretty pred)
  tyVars <- conv $ includeOnlyGradeVariables nullSpanNoFile (tyVarContext cs)

  tyVars <- conv $ tyVarContextExistential >>= includeOnlyGradeVariables nullSpanNoFile
  -- Prove the predicate
  start  <- liftIO $ Clock.getTime Clock.Monotonic
  constructors <- conv allDataConstructorNames
  (smtTime', result) <- liftIO $ provePredicate pred tyVars constructors
  -- Force the result
  _ <- return result
  end    <- liftIO $ Clock.getTime Clock.Monotonic
  let proverTime' = fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double)
  --state <- Synthesiser $ lift $ lift $ lift get
  -- traceM  $ show state
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

ctxtSubtract :: (?globals :: Globals) => Ctxt (Assumption, Structure)  -> Ctxt (Assumption, Structure) -> Synthesiser (Ctxt (Assumption, Structure))
ctxtSubtract gam [] = return gam
ctxtSubtract gam ((x, (Linear t, structure)):del) =
  case lookupAndCutout x gam of
    Just (gam', _) -> ctxtSubtract gam' del
    Nothing -> none

ctxtSubtract gam ((x, (Discharged t g2, structure)):del) =
  case lookupAndCutout x gam of
    Just (gam', (Discharged t2 g1, structure')) -> do
      g3 <- g1 `gradeSub` g2
      ctx <- ctxtSubtract gam' del
      return ((x, (Discharged t g3, structure')):ctx)
    _ -> none
    where
      gradeSub g g' = do
        -- g - g' = c
        -- therefore
        -- g = c + g'
        (kind, _, _) <- conv $ synthKind nullSpan g
        var <- conv $ freshTyVarInContext (mkId "c") kind
        conv $ existentialTopLevel var kind
        conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar var) g') g kind)
        -- maximality
        varOther' <- conv $ freshIdentifierBase "cOther"
        let varOther = mkId varOther'
        conv $ addPredicate (Impl [(varOther, kind)]
                                (Conj [Con $ ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar varOther) g') g kind])
                                (Conj [Con $ ApproximatedBy nullSpanNoFile (TyVar varOther) (TyVar var) kind]))
        return $ TyVar var

ctxtMultByCoeffect :: Type -> Ctxt (Assumption, Structure) -> Synthesiser (Ctxt (Assumption, Structure))
ctxtMultByCoeffect _ [] = return []
ctxtMultByCoeffect g1 ((x, (Discharged t g2, structure)):xs) = do
      ctxt <- ctxtMultByCoeffect g1 xs
      return ((x, (Discharged t (TyInfix TyOpTimes g1 g2), structure)): ctxt)
ctxtMultByCoeffect _ _ = none

ctxtDivByCoeffect :: (?globals :: Globals) => Type -> Ctxt (Assumption, Structure) -> Synthesiser (Ctxt (Assumption, Structure))
ctxtDivByCoeffect _ [] = return []
ctxtDivByCoeffect g1 ((x, (Discharged t g2, structure)):xs) =
    do
      ctxt <- ctxtDivByCoeffect g1 xs
      var <- gradeDiv g1 g2
      return ((x, (Discharged t var, structure)): ctxt)
  where
    gradeDiv g g' = do
      (kind, _, _) <- conv $ synthKind nullSpan g
      var <- conv $ freshTyVarInContext (mkId "c") kind
      conv $ existentialTopLevel var kind
      conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyInfix TyOpTimes g (TyVar var)) g' kind)
      return $ TyVar var
ctxtDivByCoeffect _ _ = none

ctxtMerge :: (?globals :: Globals)
          => (Type -> Type -> Type) -- lattice operator
          -> Ctxt (Assumption, Structure)
          -> Ctxt (Assumption, Structure)
          -> Synthesiser (Ctxt (Assumption, Structure))

-- Base cases
--  * Empties
ctxtMerge _ [] [] = return []

--  * Can meet/join an empty context to one that has graded assumptions
ctxtMerge operator [] ((x, (Discharged t g, structure)) : ctxt) = do
  -- Left context has no `x`, so assume it has been weakened (0 gade)
  (kind, _, _) <- conv $ synthKind nullSpan g
  ctxt' <- ctxtMerge operator [] ctxt
  return $ (x, (Discharged t g, structure)) : ctxt'
--  return $ (x, Discharged t (operator (TyGrade (Just kind) 0) g)) : ctxt'

--  * Cannot meet/join an empty context to one with linear assumptions
ctxtMerge operator [] ((x, (Linear t, structure)) : ctxt) = do
  ctxt' <- ctxtMerge operator [] ctxt
  return $ ((x, (Linear t, structure)) : ctxt')
  

-- Inductive cases
ctxtMerge operator ((x, (Discharged t1 g1, structure)) : ctxt1') ctxt2 =
  case lookupAndCutout x ctxt2 of
    Just (ctxt2', (Discharged t2 g2, structure)) ->
      if t1 == t2 -- Just in case but should always be true
        then do
          ctxt' <- ctxtMerge operator ctxt1' ctxt2'
          return $ (x, (Discharged t1 (operator g1 g2), structure)) : ctxt'

        else none

    Just (_, (Linear _, _)) -> none -- mode mismatch

    Nothing -> do
      -- Right context has no `x`, so assume it has been weakened (0 gade)
      ctxt' <- ctxtMerge operator ctxt1' ctxt2
      (kind, _, _) <- conv $ synthKind nullSpan g1
      return $ (x, (Discharged t1 g1, structure)) : ctxt'
      --return $ (x, Discharged t1 (operator g1 (TyGrade (Just kind) 0))) : ctxt'

ctxtMerge operator ((x, (Linear t1, structure)) : ctxt1') ctxt2 =
  case lookupAndCutout x ctxt2 of
    Just (ctxt2', (Linear t2, structure)) ->
      if t1 == t2 -- Just in case but should always be true
        then do
          ctxt' <- ctxtMerge operator ctxt1' ctxt2'
          return $ (x, (Linear t1, structure)) : ctxt1'
        else none

    Just (_, (Discharged{}, _)) -> none -- mode mismatch

    Nothing -> none -- Cannot weaken a linear thing

ctxtAdd :: Ctxt (Assumption, Structure) -> Ctxt (Assumption, Structure) -> Maybe (Ctxt (Assumption, Structure))
ctxtAdd [] y = Just y
ctxtAdd ((x, (Discharged t1 g1, structure)):xs) ys =
  case lookupAndCutout x ys of
    Just (ys', (Discharged t2 g2, structure')) -> do
      ctxt <- ctxtAdd xs ys'
      return $ (x, (Discharged t1 (TyInfix TyOpPlus g1 g2), structure')) : ctxt
    Nothing -> do
      ctxt <- ctxtAdd xs ys
      return $ (x, (Discharged t1 g1, structure)) : ctxt
    _ -> Nothing
ctxtAdd ((x, (Linear t1, structure)):xs) ys =
  case lookup x ys of
    Just (Linear t2, structure') -> Nothing
    Nothing -> do
      ctxt <- ctxtAdd xs ys
      return $ (x, (Linear t1, structure)) : ctxt
    _ -> Nothing



bindToContext :: (Id, (Assumption, Structure)) -> Ctxt (Assumption, Structure) -> Ctxt (Assumption, Structure) -> Bool -> (Ctxt (Assumption, Structure), Ctxt (Assumption, Structure))
bindToContext var gamma omega True = (gamma, omega ++ [var])
bindToContext var gamma omega False = (gamma ++ [var], omega)


isADTorGADT :: Type -> Maybe Id
isADTorGADT (TyCon id) = Just id
isADTorGADT (TyApp e1 e2) = isADTorGADT e1
isADTorGADT _ = Nothing


isLAsync :: Type -> Bool
isLAsync TyApp{} = True
isLAsync TyCon{} = True
isLAsync Box{}   = True
isLAsync _ = False


isZeroGrade :: Assumption -> Bool
isZeroGrade (Discharged _ (TyGrade _ 0)) = True
isZeroGrade _ = False


isAtomic :: Type -> Bool
isAtomic TyVar {} = True
isAtomic _ = False


{- 

     Given a data constructor, try to unify a fresh instance of this constructor with the assumption type. If the unification generates 
     additional constraints then these are solved locally for that type constructor. 

-}
checkConstructor :: (?globals::Globals)
      => TypeScheme 
      -> Type 
      -> Substitution 
      -> Synthesiser (Bool, Bool, Type, [Type], Substitution, Substitution)
checkConstructor con@(Forall  _ binders constraints conTy) assumptionTy subst = do
    conv $ resetAddedConstraintsFlag -- reset the flag that says if any constraints were added
    (conTyFresh, tyVarsFreshD, substFromFreshening, constraints', coercions) <- conv $ freshPolymorphicInstance InstanceQ True con subst []

    -- Take the rightmost type of the function type, collecting the arguments along the way 
    let (conTy', args) = rightMostFunTy conTyFresh
    conTy'' <- conv $ substitute coercions conTy'

    -- assumptionTy == conTy 
    (success, specTy, subst') <- conv $ equalTypes nullSpanNoFile assumptionTy conTy''
 
    -- Run the solver (i.e. to check constraints on type indexes hold)

    cs <- conv $ get
    if addedConstraints cs then do

      let predicate = Conj $ predicateStack cs
      predicate <- conv $ substitute subst' predicate
      debugM "show predicate: " (pretty predicate)
      coeffectVars <- conv $ tyVarContextExistential >>= includeOnlyGradeVariables nullSpanNoFile
      constructors <- conv$ allDataConstructorNames
      (_, result) <- conv$ liftIO $ provePredicate predicate coeffectVars constructors
      let smtResult = case result of QED -> True ; _ -> False
      debugM "smt result: " (show smtResult)

      --smtResult <- solve  -- use existing solver infrastructure 
      return (smtResult, success, specTy, args, subst', substFromFreshening)
    else return (True, success, specTy, args, subst', substFromFreshening)


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


constrArgs :: Type -> Maybe [Type]
constrArgs (TyCon _) = Just []
constrArgs (TyApp _ _) = Just []
constrArgs (FunTy _ e1 e2) = do
  res <- constrArgs e2
  return $ e1 : res
constrArgs _ = Nothing



rightMostFunTy :: Type -> (Type, [Type])
rightMostFunTy (FunTy _ _ arg t) = let (t', args) = rightMostFunTy t in (t', arg : args)
rightMostFunTy t = (t, [])

reconstructFunTy :: Type -> [Type] -> Type
reconstructFunTy = foldl (flip (FunTy Nothing Nothing))


makePattern :: Id ->  [Id] -> Maybe Type -> Pattern ()
makePattern conId vars Nothing = PConstr nullSpanNoFile () False conId (map (PVar nullSpanNoFile () False) vars)
makePattern conId vars (Just grade) = PBox nullSpanNoFile () False (PConstr nullSpanNoFile () False conId (map (PVar nullSpanNoFile () False) vars))


-- Construct a typed pattern from an untyped one from the context
transformPattern :: 
     Ctxt (Id, Type)
  -> Type 
  -> [(Id, (Assumption, Structure))] 
  -> Pattern () 
  -> Ctxt (Assumption, Structure) 
  -> Maybe (Pattern Type, Ctxt (Id, Type))
transformPattern bindings adt ctxt (PConstr s () b id pats) unboxed = do
  (pats', bindings') <- transformPatterns bindings adt ctxt pats unboxed
  Just (PConstr s adt b id pats', bindings)
transformPattern bindings adt ctxt (PVar s () b name) unboxed =
  let (pat, name', bindings') = case lookup name unboxed of
        Just (Discharged ty _, structure) -> (PBox s ty False, name, bindings)
        _ -> (id, name, bindings)
  in
  case lookup name ctxt of
     Just (Linear t, structure) -> Just (pat $ PVar s t b name', bindings')
     Just (Discharged t c, structure) -> Just (pat $ PVar s t b name', bindings')
     Nothing -> Nothing
transformPattern bindings adt ctxt (PBox s () b p) unboxed = do
  (pat', bindings') <- transformPattern bindings adt ctxt p unboxed
  Just (PBox s adt b pat', bindings')
transformPattern _ _ _ _ _ = Nothing


instance Pretty a => Pretty (Structure a) where
  pretty None    = "None"
  pretty (Arg a) = "Arg " <> pretty a
  pretty (Dec a) = "Dec " <> pretty a

bindToContext :: (Id, (Assumption, Structure Id)) -> Ctxt (Assumption, Structure Id) -> Ctxt (Assumption, Structure Id) -> Bool -> (Ctxt (Assumption, Structure Id), Ctxt (Assumption, Structure Id))
bindToContext var gamma omega True = (gamma, omega ++ [var])
bindToContext var gamma omega False = (gamma ++ [var], omega)
transformPatterns :: 
     Ctxt (Id, Type) 
  -> Type 
  -> [(Id, (Assumption, Structure))] 
  -> [Pattern ()]
  -> Ctxt (Assumption, Structure) 
  -> Maybe ([Pattern Type], Ctxt (Id, Type))
transformPatterns bindings adt ctxt [] unboxed = Just ([], bindings)
transformPatterns bindings adt ctxt (p:ps) unboxed = do
  (pat, bindings') <- transformPattern bindings adt ctxt p unboxed
  (res, bindingsFinal) <- transformPatterns bindings' adt ctxt ps unboxed
  return (pat:res, bindingsFinal)


-- Note that the way this is used, the (var, assumption) pair in the first
-- argument is not contained in the provided context (second argument)
useVar :: (?globals :: Globals)
  => (Id, (Assumption, Structure))
  -> Ctxt (Assumption, Structure)
  -> ResourceScheme PruningScheme
  -> Maybe Type -- Grade on rule style of synthesis 
  -> Synthesiser (Bool, Ctxt (Assumption, Structure), Type)
-- Subtractive
useVar (name, (Linear t, _)) gamma Subtractive _ = return (True, gamma, t)
useVar (name, (Discharged t grade, structure)) gamma Subtractive Nothing = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  var <- freshIdentifier 
  conv $ existentialTopLevel var kind -- Existentials must be at the topLevel because they may be generated inside an implication but may occur outside of the implication 
  conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar var) (TyGrade (Just kind) 1)) grade kind)
  res <- solve
  if res then
    return (True, replace gamma name (Discharged t (TyVar var), structure), t) else
    return (False, [], t)
useVar (name, (Discharged t grade, structure)) gamma Subtractive (Just grade') = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  var <- freshIdentifier -- conv $ freshTyVarInContext (mkId "c") kind
  conv $ existentialTopLevel var kind
  conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar var) grade') grade kind)
  res <- solve
  if res then
    return (True, replace gamma name (Discharged t (TyVar var), structure), t) else
    return (False, [], t)

-- Additive
useVar (name, (Linear t, structure)) _ Additive{} _ = return (True, [(name, (Linear t, structure))], t)
useVar (name, (Discharged t grade, structure)) _ Additive{} Nothing = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  return (True, [(name, (Discharged t (TyGrade (Just kind) 1), structure))], t)
useVar (name, (Discharged t grade, structure)) _ Additive{} (Just grade') = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  return (True, [(name, (Discharged t  grade', structure))], t)


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
  => Ctxt (Assumption, Structure)
  -> Ctxt (Assumption, Structure)
  -> Ctxt (Assumption, Structure)
  -> ResourceScheme PruningScheme
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure), Substitution, Bindings, Bool)
varHelper gamma left [] _ _ _ _ = none
varHelper gamma left (assumption@(id, (a, structure)) : right) resourceScheme focusPhase grade goal@(Goal (goalTySch@(Forall _ _ _ goalTy)) _) =
  varHelper gamma (assumption:left) right resourceScheme focusPhase grade goal `try` do
    debugM "synthDebug - inside varHelper checking assumption: " (show assumption <> " against goal " <> show goalTy)
    conv $ resetAddedConstraintsFlag -- reset the flag that says if any constraints were added
    (success, specTy, subst) <- conv $ equalTypes nullSpanNoFile (getAssumptionType a) goalTy
    if success then do
      -- see if any constraints were added
      st <- conv $ get
      solved <- if addedConstraints st
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
  => Ctxt TypeScheme
  -> Ctxt TypeScheme
  -> Ctxt (Assumption, Structure)
  -> Ctxt (Assumption, Structure)
  -> ResourceScheme PruningScheme
  -> Bool
  -> Bool
  -> Depth
  -> FocusPhase     
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure), Substitution, Bindings, Bool)
defHelper _ [] _ _ _ _ _ _ _ _ _ = none

defHelper left (def@(x, defTySch):right) gamma omega Subtractive inDef canDef depth focusPhase grade goal@(Goal goalTySch@(Forall _ binders constraints ty) structure) =
 defHelper (def:left) right gamma omega Subtractive inDef True depth focusPhase grade goal `try`
  (case defTySch of
    (Forall _ _ _ (FunTy{})) -> do

      state <- Synthesiser $ lift $ lift $ get

      -- Only try the def if we haven't hit the def allowed depth 
      if (appCurr depth) <= (appMax depth) && (canDef || not (x `elem` currDef state)) then do
        (freshTy, tyVarsFreshD, substFromFreshening, constraints', _) <- conv $ freshPolymorphicInstance InstanceQ False defTySch [] [] 
        case freshTy of 
          (FunTy _ tyA tyB) -> do 
            debugM "synthDebug - (def) in defHelper attempting to use  def: " (pretty def <> " towards goal: " <> pretty goalTySch)

            y <- freshIdentifier
        
            let (gamma', omega') = bindToContext (y, (Linear tyB, None)) gamma omega True

            (e1, delta1, subst1, bindings1, structurallyDecr1) <- synthesiseInner (def:left ++ right) Subtractive True True (depth { appCurr = (appCurr depth) + 1 }) focusPhase gamma' omega' grade goal 

            case lookup y delta1 of
              Nothing -> do
            
                (e2, delta2, subst2, bindings2, structurallyDecr2) <- synthesiseInner (def:left ++ right) Subtractive True True (depth { appCurr = (appCurr depth) + 1 }) (Focus R Sync) delta1 [] grade (Goal (Forall nullSpanNoFile binders constraints tyA) structure) 

                debugM "synthDebug - (def) e1: " (pretty e1)
                debugM "synthDebug - (def) making a: " (pretty $ Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTySch tyA) y e1)
                debugM "synthDebug - (def) delta1: " (show delta1)
                debugM "synthDebug - (def) delta2: " (show delta2)
                debugM "synthDebug - (def) structurallydecr1: " (show structurallyDecr1)
                debugM "synthDebug - (def) structurallydecr2: " (show structurallyDecr2)

                -- At least one of the sub-components of the application must be structurally decreasing
                if structurallyDecr1 || structurallyDecr2 || not (x `elem` currDef state) then do 
--                  _ <- error "hello"
                  -- liftIO $ putStrLn ("making a: " <> (pretty $ Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTySch tyA) y e1))
                  substOut <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
                  return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTySch tyA) y e1, delta2, substOut, bindings1 ++ bindings2, True)
                else none
              _ -> none
          _ -> none
      else none
    _ -> none)
defHelper left (def@(x, defTySch) : right) gamma omega add@(Additive mode) inDef canDef depth focusPhase grade goal@(Goal goalTySch@(Forall _ binders constraints ty) structure) =
 defHelper (def:left) right gamma omega add inDef True depth focusPhase grade goal `try`
 (case defTySch of
    (Forall _ _ _ (FunTy _ _ _)) -> do      

      state <- Synthesiser $ lift $ lift $ get

      -- Only try the def if we haven't hit the def allowed depth 
      if (appCurr depth) <= (appMax depth) && (canDef || not (x `elem` currDef state)) then do
        (freshTy, tyVarsFreshD, substFromFreshening, constraints', _) <- conv $ freshPolymorphicInstance InstanceQ False defTySch [] [] 
        case freshTy of 
          (FunTy _ tyA tyB) -> do 
            debugM "synthDebug - (def) in defHelper attempting to use  def: " (pretty def <> " towards goal: " <> pretty goalTySch)
        
            y <- freshIdentifier
            let (gamma', omega') = bindToContext (y, (Linear tyB, None)) gamma omega True
            (e1, delta1, subst1, bindings1, structurallyDecr1) <- synthesiseInner (def:left ++ right) add True True (depth { appCurr = (appCurr depth) + 1 }) focusPhase gamma' omega' grade goal

            debugM "synthDebug - (def) e1: " (pretty e1)
            debugM "synthDebug - (def) gamma' " (show gamma')
            debugM "synthDebug - (def) onega' " (show omega')
            debugM "synthDebug - (def) tyA " (show tyA)
            cs <- conv $ get
            debugM "synthDebug - (def) tyVarContext " (show (tyVarContext cs))
            debugM "synthDebug - (def) tyA " (show tyA)
            debugM "synthDebug - (def) tyB " (show tyB)
            case lookupAndCutout y delta1 of
              Just (delta1', (Linear _, _)) -> do
                gamma2 <-
                  case mode of
                    NonPruning -> return (omega ++ gamma')
                    Pruning    -> ctxtSubtract (omega ++ gamma') delta1'

                debugM "synthDebug - (def) gamma2: " (show gamma2)
                debugM "synthDebug - (def) e1: " (pretty e1)
                debugM "synthDebug - (def) delta1: " (show delta1)


                (e2, delta2, subst2, bindings2, structurallyDecr2) <- synthesiseInner (def:left ++ right) add True True (depth { appCurr = (appCurr depth) + 1 }) (Focus R Sync) gamma2 [] grade (Goal (Forall nullSpanNoFile binders constraints tyA) structure)
           
                debugM "synthDebug - (def) delta1: " (show delta1)
                debugM "synthDebug - (def) making a: " (pretty $ Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTySch tyA) y e1)
                debugM "synthDebug - (def) delta2: " (show delta2)
                debugM "synthDebug - (def) structurallydecr1: " (show structurallyDecr1)
                debugM "synthDebug - (def) structurallydecr2: " (show structurallyDecr2)

                -- At least one of the sub-components of the application must be structurally decreasing
                if structurallyDecr1 || structurallyDecr2 || not (x `elem` currDef state) then do

                  -- Add the results
                  deltaOut <- maybeToSynthesiser $ ctxtAdd delta1' delta2
                  substOut <- conv $ combineSubstitutions nullSpan subst1 subst2
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
  => Ctxt TypeScheme
  -> Ctxt (Assumption, Structure)
  -> Ctxt (Assumption, Structure)
  -> ResourceScheme PruningScheme
  -> Bool
  -> Bool 
  -> Depth
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure), Substitution, Bindings, Bool)
absHelper defs gamma omega resourceScheme inDef canDef depth focusPhase grade goal@(Goal goalTySch@(Forall _ binders constraints (FunTy name tyA tyB)) structure) = do
  -- Fresh var
  id <- useBinderNameOrFreshen name
  -- Build recursive context depending on focus mode
  let (gamma', omega') = bindToContext (id, (Linear tyA, NonDecreasing)) gamma omega (isLAsync tyA) 

  -- Synthesis body
  debugM "synthDebug" $ "(abs) lambda-binding " ++ pretty [(id, Linear tyA)]
  (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs resourceScheme inDef canDef depth focusPhase gamma' omega' grade (Goal (Forall nullSpanNoFile binders constraints tyB) structure)
  debugM "synthDebug" $ "(abs) made a lambda: " ++ pretty (makeAbs id e goalTySch)
  debugM "synthDebug" $ "(abs) delta: " ++ show delta

  -- Check resource use at the end
  case (resourceScheme, lookupAndCutout id delta) of
    (Additive{}, Just (delta', (Linear _, _))) -> 
      return (makeAbs id e goalTySch, delta', subst, bindings, structurallyDecr)
    (Subtractive, Nothing) ->
      return (makeAbs id e goalTySch, delta, subst, bindings, structurallyDecr)
    _ -> none
absHelper _ _ _ _ _ _ _ _ _ _ = none


appHelper :: (?globals :: Globals)
  => Ctxt TypeScheme
  -> Ctxt (Assumption, Structure)
  -> Ctxt (Assumption, Structure)
  -> Ctxt (Assumption, Structure)
  -> ResourceScheme PruningScheme
  -> Bool
  -> Bool
  -> Depth
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure), Substitution, Bindings, Bool)
appHelper _ _ _ [] _ _ _ _ _ _ _ = none
{-
Subtractive

x2 ∉ Δ1
Γ, x2 : B ⊢ C ⇒ t1 ; Δ1
Δ1 ⊢ A ⇒ t2 ; Δ2
------------------------ :: app
Γ, x1 : A → B ⊢ C ⇒ [(x1 t2) / x2] t1 ; Δ2

-}
appHelper defs gamma left (assumption@(x, (ty, _)) : right) Subtractive inDef canDef depth focusPhase grade goal@(Goal goalTySch@(Forall _ binders constraints _) _) =
  appHelper defs gamma (assumption : left) right Subtractive inDef canDef depth focusPhase grade goal `try`
  (case getAssumptionType ty of
    (FunTy _ tyA tyB) -> do
      -- Only try the app if we haven't hit the app allowed depth 
      if (appCurr depth) <= (appMax depth) then do

        debugM "synthDebug - (app) trying to use a function " (show assumption ++ " to get goal " ++ pretty goalTySch)

        let omega = left ++ right
        (canUse, leftOver, _) <- useVar assumption omega Subtractive grade
        if canUse 
          then do

            y <- freshIdentifier
            -- Extend context (focused) with x2 : B
            let (gamma'', omega'') = bindToContext (y, (Linear tyB, None)) gamma leftOver True

            -- let (gamma'', omega'') = case lookupAndCutout x omega' of 
            --                Just (omega'', var) -> (gamma', omega'')
            --                _ -> (gamma', omega')


            debugM "synthDebug - (app) try to synth the goal " (pretty goalTySch ++ "\n under context of gamma'': " ++ (show gamma'') ++ "\n , omega'': " ++ (show omega''))
            (e1, delta1, subst1, bindings1, structurallyDecr1) <- synthesiseInner defs Subtractive inDef True (depth { appCurr = (appCurr depth) + 1 }) focusPhase gamma'' omega'' grade goal
            case lookup y delta1 of
              Nothing -> do
                debugM "synthDebug - (app) try to synth the argument at type "  (pretty tyA)

                -- Synthesise the argument
                (e2, delta2, subst2, bindings2, structurallyDecr2) <- synthesiseInner defs Subtractive inDef True (depth { appCurr = (appCurr depth) + 1 }) (Focus R Sync) delta1 [] grade (Goal (Forall nullSpanNoFile binders constraints tyA) NonDecreasing)
                debugM "synthDebug - (app) made an e2: " (pretty $ Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTySch tyA) y e1)

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
appHelper defs gamma left (assumption@(x, (ty, _)) : right) add@(Additive mode) inDef canDef depth focusPhase grade goal@(Goal goalTySch@(Forall _ binders constraints _) _) =
  appHelper defs gamma (assumption : left) right add inDef canDef depth focusPhase grade goal `try`
  (case getAssumptionType ty of
    (FunTy _ tyA tyB) -> do
      -- Only try the app if we haven't hit the app allowed depth 
      if (appCurr depth) <= (appMax depth) then do

        let omega = (left ++ right)
        (canUse, used, _) <- useVar assumption omega add grade

        if canUse
          then do
            -- leftOverOmega <- ctxtSubtract omega used 

            y <- freshIdentifier
            -- Extend context (focused) with x2 : B
            let (gamma', omega') = bindToContext (y, (Linear tyB, None)) gamma omega True

            -- let gamma'' = case lookupAndCutout x gamma' of 
            --         Just (restOfGamma, (ty', _)) -> restOfGamma ++ [(x, (ty', Decreasing))]
            --         _ -> gamma'

            (e1, delta1, subst1, bindings1, structurallyDecr1) <- synthesiseInner defs add inDef True (depth { appCurr = (appCurr depth) + 1 }) focusPhase gamma' omega' grade goal 
              -- Make sure that `x2` appears in the result
            case lookupAndCutout y delta1 of
              Just (delta1',  (Linear _, _)) -> do

                -- Pruning subtraction
                gamma2 <- case mode of
                      NonPruning -> return (omega ++ gamma')
                      Pruning    -> ctxtSubtract (omega ++ gamma') delta1'

                  -- Synthesise the argument
                (e2, delta2, subst2, bindings2, structurallyDecr2) <- synthesiseInner defs add inDef True (depth { appCurr = (appCurr depth) + 1 }) (Focus R Sync) gamma2 [] grade (Goal (Forall nullSpanNoFile binders constraints tyA) NonDecreasing)
                debugM "synthDebug - (app) made an e2: " (pretty $ Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTySch tyA) y e1)

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
  => Ctxt TypeScheme
  -> Ctxt (Assumption, Structure)
  -> ResourceScheme PruningScheme
  -> Bool
  -> Bool
  -> Depth 
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure), Substitution, Bindings, Bool)
boxHelper defs gamma resourceScheme inDef canDef depth focusPhase grade (Goal goalTySch@(Forall _ binders constraints (Box g t)) _) = 
  let newGrade = case grade of {Just grade' -> Just $ TyInfix TyOpTimes grade' g ; Nothing -> Nothing}
  in case resourceScheme of
      Additive{} -> do
        (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs resourceScheme inDef True depth focusPhase gamma [] newGrade (Goal (Forall nullSpanNoFile binders constraints t) NonDecreasing) 
        deltaOut <- case newGrade of {Just _ -> return delta ; Nothing -> ctxtMultByCoeffect g delta}
        return (makeBox goalTySch e, deltaOut, subst, bindings, structurallyDecr)
      Subtractive -> do
        (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs resourceScheme inDef True depth focusPhase gamma [] newGrade (Goal (Forall nullSpanNoFile binders constraints t) NonDecreasing)
        deltaOut <- case newGrade of
            Just _ -> return delta
            Nothing -> do
              used <- ctxtSubtract gamma delta
              -- Compute what was used to synth e
              delta' <- ctxtMultByCoeffect g used
              ctxtSubtract gamma delta'
        res <- solve
        boolToSynthesiser res (makeBox goalTySch e, deltaOut, subst, bindings, structurallyDecr)
boxHelper _ _ _ _ _ _ _ _ _ = none


unboxHelper :: (?globals :: Globals)
  => Ctxt TypeScheme
  -> Ctxt (Assumption, Structure)
  -> Ctxt (Assumption, Structure)
  -> Ctxt (Assumption, Structure)
  -> ResourceScheme PruningScheme
  -> Bool
  -> Bool
  -> Depth  
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure), Substitution, Bindings, Bool)
unboxHelper _ _ _ [] _ _ _ _ _ _ _ = none
{-
Subtractive
0 <= s
Γ, x2 : [A] r ⊢ B ⇒ e ; Δ, x2 : [A] s
-------------------------------------------- :: unbox
Γ, x1 : [] r A ⊢ B ⇒ let [x2] = x1 in e; Δ

-}
unboxHelper defs gamma left (assumption@(x, (ty, structure)) : right) Subtractive False canDef depth focusPhase grade goal@(Goal goalTySch _) =
  unboxHelper defs gamma (assumption : left) right Subtractive False canDef depth focusPhase grade goal `try`
    (case ty of
      Linear (Box grade_r tyA) -> do

        debugM "synthDebug" $ "Trying to unbox " ++ show assumption

        let omega = left ++ right
        (canUse, leftOver, _) <- useVar assumption omega Subtractive grade
        if canUse then do
          ---
          y <- freshIdentifier
          let (gamma', omega') = bindToContext (y, (Discharged tyA grade_r, structure)) gamma leftOver (isLAsync tyA)
          debugM "synthDebug" $ "Inside unboxing try to synth for " ++ pretty goalTySch ++ " under " ++ pretty [(y, Discharged tyA grade_r)]

          (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs Subtractive False canDef depth focusPhase gamma' omega' grade goal
          ---
          case lookupAndCutout y delta of
            Just (delta', (Discharged _ grade_s, _)) -> do
              -- Check that: 0 <= s
              (kind, _, _) <- conv $ synthKind nullSpan grade_s
              conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade_s kind)
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
          let (gamma', omega') = bindToContext (y, (Discharged tyA (TyInfix TyOpTimes grade_r grade_s), structure)) gamma omega (isLAsync tyA) 
          (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs Subtractive False canDef depth focusPhase gamma' omega' grade goal 
          case lookupAndCutout y delta of
            Just (delta', (Discharged _ grade_s', _)) ->  do 
              (kind, _, _) <- conv $ synthKind nullSpan grade_s'
              r' <- freshIdentifier 
              conv $ existentialTopLevel r' kind
              conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyInfix TyOpTimes (TyVar r') grade_s) grade_s' kind)
              res <- solve 
              debugM "synthDebug - (unbox - double) term: " (pretty $ makeUnbox y x goalTySch (Box grade_r tyA) tyA e)
              boolToSynthesiser res (makeUnbox y x goalTySch (Box grade_r tyA) tyA e, replace delta' x (Discharged (Box grade_r tyA) (TyVar r'), structure), subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr)
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
unboxHelper defs gamma left (assumption@(x, (ty, structure)) : right) add@(Additive{}) False canDef depth focusPhase grade goal@(Goal goalTySch _) =
  unboxHelper defs gamma (assumption : left) right add False canDef depth focusPhase grade goal `try`
   (case ty of
     (Linear (Box grade_r tyA)) -> do
       let omega = left ++ right
       (canUse, used, t) <- useVar assumption omega add grade
       if canUse
          then do
            y <- freshIdentifier
            -- omega1 <- ctxtSubtract omega omega'
            let (gamma', omega') = bindToContext (y, (Discharged tyA grade_r, structure)) gamma omega (isLAsync tyA)

            -- Synthesise the body of a `let` unboxing
            (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs add False canDef depth focusPhase gamma' omega' grade goal

            -- Add usage at the binder to the usage in the body
            delta' <- maybeToSynthesiser $ ctxtAdd used delta

            case lookupAndCutout y delta' of
              Just (delta'', (Discharged _ grade_s, _)) -> do
                (kind, _, _) <- conv $ synthKind nullSpan grade_r
                conv $ addConstraint (ApproximatedBy nullSpanNoFile grade_s grade_r kind)
                res <- solve
                boolToSynthesiser res (makeUnbox y x goalTySch tyA (Box grade_r tyA) e,  delta'', subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr) 
              _ -> do
                (kind, _, _) <- conv $ synthKind nullSpan grade_r
                conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade_r kind)
                res <- solve
                boolToSynthesiser res (makeUnbox y x goalTySch tyA (Box grade_r tyA) e,  delta', subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr) 
          else none
     (Discharged (Box grade_r tyA) grade_s) -> do
        let omega = left ++ right
        (canUse, _, _) <- useVar assumption [] add grade
        if canUse then do
          y <- freshIdentifier
          let (gamma', omega') = bindToContext (y, (Discharged tyA (TyInfix TyOpTimes grade_r grade_s), structure)) gamma omega (isLAsync tyA)
          (e, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs add False canDef depth focusPhase gamma' omega' grade goal 
          case lookupAndCutout y delta of
            Just (delta', (Discharged _ grade_s', _)) ->  do
              (kind, _, _) <- conv $ synthKind nullSpan grade_s'
              r' <- freshIdentifier 
              conv $ existentialTopLevel r' kind
              conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyInfix TyOpTimes (TyVar r') grade_s) (TyInfix TyOpTimes grade_r grade_s) kind)
              conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyInfix TyOpTimes (TyVar r') grade_s) grade_s' kind)
              res <- solve
              boolToSynthesiser res (makeUnbox y x goalTySch (Box grade_r tyA) tyA e, replace delta x (Discharged (Box grade_r tyA) (TyVar r'), structure), subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr)
            _ -> do
                (kind, _, _) <- conv $ synthKind nullSpan grade_r
                conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) (TyInfix TyOpTimes grade_r grade_s) kind)
                res <- solve
                boolToSynthesiser res (makeUnbox y x goalTySch (Box grade_r tyA) tyA e, delta, subst, (x, (y, Box grade_r tyA)):bindings, structurallyDecr)
        else none

     _ -> none)

unboxHelper _ _ _ _ _ _ _ _ _ _ _ = none


constrIntroHelper :: (?globals :: Globals)
  => Ctxt TypeScheme
  -> Ctxt (Assumption, Structure)
  -> ResourceScheme PruningScheme
  -> Bool
  -> Bool
  -> Depth 
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure), Substitution, Bindings, Bool)
constrIntroHelper defs gamma resourceScheme False canDef depth focusPhase grade goal@(Goal goalTySch@(Forall s binders constraints tyA) structure) =
  case (isADTorGADT tyA) of
    Just name -> do

      state <- Synthesiser $ lift $ lift $ get

      if (iCurr depth) < (iMax depth) || not (isRecursiveType (Just name) (constructors state)) then do


        debugM "synthDebug - entered constrIntroHelper with goal: " (show goal)
        debugM "synthDebug - entered constrIntroHelper with gamma: " (show gamma)

        let (recursiveCons, nonRecursiveCons) = relevantConstructors name (constructors state)
        let sortedCons = sortBy compareArity nonRecursiveCons ++ sortBy compareArity recursiveCons

        -- For each relevent data constructor, we must now check that it's type matches the goal
        (maybeExpr, deltaOut, substOut, bindingsOut, structurallyDecrOut) <- foldM (\ a (conName, (conTySch@(Forall s conBinders conConstraints conTy), conSubst)) -> do
          case a of 
            (Nothing, [], [], [], False) -> do
              conv $ newConjunct
              result <- checkConstructor conTySch tyA conSubst
              conv $ newConjunct
              case result of
                (True, True, specTy, _, specSubst, substFromFreshening) -> do
            --      _ <- conv $ localState
                  specTy' <- conv $ substitute substFromFreshening specTy
                  subst' <- conv $ combineSubstitutions s conSubst specSubst
                  specTy'' <- conv $ substitute subst' specTy'
                  debugM "synthDebug - constrIntroHelper - synthing arguments for: " (show conName)
                  case constrArgs conTy of 
                    Just [] -> do 
                      let delta = case resourceScheme of {Additive{} -> []; Subtractive{} -> gamma}
                      conv $ concludeImplication nullSpanNoFile [] 
                      return (Just $ makeNullaryConstructor conName, delta, conSubst, [], False) `try` return a
                    Just conArgs -> do 
                      args <- conv $ mapM (\s -> do 
                        s' <- substitute substFromFreshening s
                        s'' <- substitute specSubst s'
                        return (s'', boolToStructure $ isDecreasing name [s])) conArgs

                      (exprs, delta, subst, bindings, structurallyDecr) <- synthConArgs name (constructors state) defs args conBinders conConstraints conSubst
                      conv $ concludeImplication nullSpanNoFile [] 
                      return (Just $ makeConstr exprs conName conTy, delta, subst, bindings, structurallyDecr) `try` return a
                    Nothing -> do
                      conv $ concludeImplication nullSpanNoFile [] 
                      return a
                _ -> do
                  conv $ concludeImplication nullSpanNoFile [] 
                  return a
            res -> return res) (Nothing, [], [], [], False) sortedCons   
        case maybeExpr of  
          Just expr -> return (expr, deltaOut, substOut, bindingsOut, False)
          _ -> none
      else none
    _ -> none
  where


    -- Traverse the argument types to the constructor and synthesise a term for each one
    synthConArgs tyAName consGlobal defs [(argTyA, isDecr)] conBinders conConstraints conSubst = do
      (expr, delta, subst, bindings, structurallyDecr) <- synthesiseInner defs resourceScheme False True (if isRecursiveType (Just tyAName) consGlobal then depth { iCurr = (iCurr depth) + 1 } else depth) (Focus R Async) gamma [] grade (Goal (Forall s conBinders conConstraints argTyA) isDecr)
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
      (expr, delta, subst, bindings', structurallyDecr') <- synthesiseInner defs resourceScheme False True (if isRecursiveType (Just tyAName) consGlobal then depth { iCurr = (iCurr depth) + 1 } else depth) (Focus R Async) gamma' [] grade (Goal (Forall s conBinders conConstraints argTyA) isDecr)
      subst'' <- conv $ combineSubstitutions nullSpanNoFile subst substs'
      delta' <- case resourceScheme of
            Additive{} -> maybeToSynthesiser $ ctxtAdd deltas delta
            Subtractive -> return delta
      return ((expr, argTyA):exprs, delta', subst'', bindings ++ bindings', structurallyDecr || structurallyDecr')
    synthConArgs _ _ _ _ _ _ _ = none

    boolToStructure False = NonDecreasing
    boolToStructure True  = Decreasing

constrIntroHelper _ _ _ _ _ _ _ _ _ = none

{- 

Constructor elimination
=======================

LINEAR BASE

GRADED BASE

  * Additive:

    C : B₁ʳ¹ → .. Bₙⁿ¹ → KA) ∈ D
    ----------------------------------------------------------------------------------------------- :: CaseGraded
    Γ, x : ☐ᵣ KA ⊢ₛ B' ⇒ case x of C yⁱ₁ .. yⁱₙ → t; (Δ\y¹₁ .. \y¹ₙ) ⊔ (Δ\yⁿ₁ .. \yⁿₙ)  + x : ☐ᵣ A



-}
constrElimHelper :: (?globals :: Globals)
  => Ctxt TypeScheme
  -> Ctxt (Assumption, Structure)
  -> Ctxt (Assumption, Structure)
  -> Ctxt (Assumption, Structure)
  -> ResourceScheme PruningScheme
  -> Bool 
  -> Bool
  -> Depth
  -> FocusPhase
  -> Maybe Type
  -> Goal
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure), Substitution, Bindings, Bool)
constrElimHelper _ _ _ [] _ _ _ _ _ _ _ = none
constrElimHelper defs gamma left (assumption@(x, (tyA, structure)):right) mode False canDef depth focusPhase grade goal@(Goal goalTySch@(Forall _ _ _ tyB) _) =
  constrElimHelper defs gamma (assumption:left) right mode False canDef depth focusPhase grade goal `try` do
    state <- Synthesiser $ lift $ lift $ get
    if (eCurr depth) < (eMax depth) || not (isRecursiveType (isADTorGADT $ getAssumptionType tyA) (constructors state))  then do
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
              conv newConjunct 
              result <- checkConstructor conTySch assumptionTy conSubst
              conv newConjunct 
              case result of 
                (True, True, specTy, conTyArgs, conSubst', _) -> do

                  -- Calculate assumptions
                  assumptions <- mapM (\ arg -> do
                    y <- freshIdentifier 
                    arg' <- conv $ substitute conSubst' arg
                    let assumptionType = case assumptionGrade of {Nothing -> Linear arg'; Just grade_r -> Discharged arg' grade_r}
                    let assumption = if isRecursiveCon name (y, (Forall nullSpanNoFile binders constraints arg, [])) then (y, (assumptionType, Decreasing)) else (y, (assumptionType, NonDecreasing))
                    return assumption) conTyArgs
                  
                  let (vars, _) = unzip assumptions
                  let constrElimPattern = makePattern conId vars grade


                  (gamma', omega') <- 
                    case mode of 
                      Additive{} -> do 
                        usageOut' <- ctxtSubtract (assumption:gamma) usageOut
                        return (gamma, omega)
                      Subtractive -> 
                        case lookupAndCutout x usageOut of 
                          Just (usageOut', (ty', structure')) -> return ((x, (ty', Decreasing)):gamma, usageOut')
                          _ -> return (gamma, usageOut)                  
                  let (gamma'', omega'', unboxed) = bindAssumptions (elimDepthReached state) [] assumptions gamma' omega'

                  debugM "synthDebug - (conElim) trying con: " (pretty conId)
                  debugM "synthDebug - (conElim) gamma: " (show gamma'')
                  debugM "synthDebug - (conElim) gamma: " (show omega'')

                  (expr, delta, subst, bindings, structurallyDecr') <- synthesiseInner defs mode False canDef (if isRecursiveType (Just name) (constructors state) then depth { eCurr = (eCurr depth) + 1} else depth) focusPhase gamma'' omega'' grade goal 

                  delta' <- checkAssumptions (x, assumptionTy) mode delta assumptions unboxed
                  case transformPattern bindings assumptionTy (gamma'' ++ omega'') constrElimPattern unboxed of
                    Just (pattern, bindings') ->
                      let mergeOp = case mode of Additive{} -> TyInfix TyOpJoin ; _ -> TyInfix TyOpMeet in do
                        returnDelta <- if index == 0 then return delta' else ctxtMerge mergeOp deltas delta' 
                        conv $ concludeImplication nullSpanNoFile [] 
                        returnSubst <- conv $ combineSubstitutions nullSpanNoFile subst substs
                        return ((pattern, expr):exprs, returnDelta, returnSubst, bindings ++ bindings', structurallyDecr || structurallyDecr', index + 1)
                    Nothing -> do 
                      conv $ concludeImplication nullSpanNoFile [] 
                      return (exprs, deltas, substs, bindings, structurallyDecr, index)
                _ -> do 
                  debugM "synthDebug - (conElim) FAILED con: " (pretty conId)
                  conv $ concludeImplication nullSpanNoFile [] 
                  return (exprs, deltas, substs, bindings, structurallyDecr, index)
              ) ([], [], [], [], False, 0) sortedCons
            case patterns of 
              (_:_) -> do 
                debugM "made: " (pretty $ makeCase assumptionTy x patterns tyB assumptionGrade)
             --   _ <- error "errorrr"
                finDelta <- case (mode, assumptionGrade) of {(Additive{}, Nothing) -> maybeToSynthesiser $ ctxtAdd usageOut delta; _ -> return delta}
                return (makeCase assumptionTy x patterns tyB assumptionGrade, finDelta, resSubst, resBindings, structurallyDecr)
              _ -> none
          _ -> none   
      else none
    else none

  where 
    
  bindAssumptions :: Bool
    -> Ctxt (Assumption, Structure)
    -> Ctxt (Assumption, Structure)
    -> Ctxt (Assumption, Structure)
    -> Ctxt (Assumption, Structure)
    -> (Ctxt (Assumption, Structure), Ctxt (Assumption, Structure), Ctxt (Assumption, Structure))
  bindAssumptions depthReached unboxed [] gamma omega = (gamma, omega, unboxed)

  bindAssumptions True unboxed (assumption@(id, (Linear t, structure)):assmps) gamma omega =
    let (gamma', omega') = bindToContext assumption gamma omega False in
    bindAssumptions True unboxed assmps gamma' omega' 
  bindAssumptions False unboxed (assumption@(id, (Linear t, structure)):assmps) gamma omega =
    let (gamma', omega') = bindToContext assumption gamma omega (isLAsync t) in
    bindAssumptions False unboxed assmps gamma' omega' 

  bindAssumptions True unboxed (assumption@(id, (Discharged (Box grade t) grade', structure)):assmps) gamma omega =
    let (gamma', omega') = bindToContext (id, (Discharged t (TyInfix TyOpTimes grade grade'), structure)) gamma omega False in
    bindAssumptions True ((id, (Discharged t (TyInfix TyOpTimes grade grade'), structure)):unboxed) assmps gamma' omega' 
  bindAssumptions False unboxed (assumption@(id, (Discharged (Box t grade) grade', structure)):assmps) gamma omega =
    let (gamma', omega') = bindToContext (id, (Discharged t (TyInfix TyOpTimes grade grade'), structure)) gamma omega (isLAsync t) in
    bindAssumptions False ((id, (Discharged t (TyInfix TyOpTimes grade grade'), structure)):unboxed) assmps gamma' omega' 

  bindAssumptions True unboxed (assumption@(id, (Discharged t _,  structure)):assmps) gamma omega =
    let (gamma', omega') = bindToContext assumption gamma omega False in
    bindAssumptions True unboxed assmps gamma' omega' 
  bindAssumptions False unboxed (assumption@(id, (Discharged t _, structure)):assmps) gamma omega =
    let (gamma', omega') = bindToContext assumption gamma omega (isLAsync t) in
    bindAssumptions False unboxed assmps gamma' omega' 


  checkAssumptions :: (?globals::Globals) 
    => (Id, Type)
    -> ResourceScheme PruningScheme
    -> [(Id, (Assumption, Structure))]
    -> [(Id, (Assumption, Structure))]
    -> Ctxt (Assumption, Structure) -> Synthesiser [(Id, (Assumption, Structure))]
  checkAssumptions _ mode del [] _ = return del
  checkAssumptions x sub@Subtractive{} del ((id, (Linear t, structure)):assmps) unboxed =
    case lookup id del of
      Nothing -> checkAssumptions x sub del assmps unboxed
      _ -> none
  checkAssumptions (x, t') sub@Subtractive{} del ((id, (Discharged t g, structure)):assmps) unboxed =
    case lookupAndCutout id del of
      Just (del', (Discharged _ g', structure)) ->
        case lookup id unboxed of
          Just (Discharged _ g'', structure) -> do
            del'' <- checkAssumptions (x, t') sub del' assmps unboxed
            (kind, _, _) <- conv $ synthKind nullSpan g'
            conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) g' kind)
            res <- solve
            if res then do
              ctxtMerge (TyInfix TyOpMeet) [(x, (Discharged t' g, structure))] del''
            else none
          _ -> do
            del'' <- checkAssumptions (x, t') sub del' assmps unboxed
            (kind, _, _) <- conv $ synthKind nullSpan g'
            conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) g' kind)
            res <- solve
            if res then
              ctxtMerge (TyInfix TyOpMeet) [(x, (Discharged t' g', structure))] del''
            else none
      _ -> none
  checkAssumptions x add@Additive{} del ((id, (Linear t, structure)):assmps) unboxed =
    case lookupAndCutout id del of
      Just (del', _) ->
        checkAssumptions x add del' assmps unboxed
      _ -> none
  checkAssumptions (x, t') add@Additive{} del ((id, (Discharged t g, structure)):assmps) unboxed = do
        case lookupAndCutout id del of
          Just (del', (Discharged _ g', structure)) ->
            case lookup id unboxed of
              Just (Discharged _ g'', structure) -> do
                del'' <- checkAssumptions (x, t') add del' assmps unboxed
                (kind, _, _) <- conv $ synthKind nullSpan g'
                conv $ addConstraint (ApproximatedBy nullSpanNoFile g' g'' kind)
                res <- solve
                if res then do
                  ctxtMerge (TyInfix TyOpJoin) [(x, (Discharged t' g, structure))] del''
                else none
              _ -> (do
                del'' <- checkAssumptions (x, t') add del' assmps unboxed
                (kind, _, _) <- conv $ synthKind nullSpan g'
                conv $ addConstraint (ApproximatedBy nullSpanNoFile g' g kind)
                res <- solve
                if res then 
                  ctxtMerge (TyInfix TyOpJoin) [(x, (Discharged t' g', structure))] del''
                else none)
          _ -> do
            (kind, _, _) <- conv $ synthKind nullSpan g
            conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) g kind)
            res <- solve
            if res then checkAssumptions (x, t') add del assmps unboxed else none

constrElimHelper _ _ _ _ _ _ _ _ _ _ _ = none



synthesiseInner :: (?globals :: Globals)
           => Ctxt TypeScheme
           -> ResourceScheme PruningScheme       
           -> Bool
           -> Bool
           -> Depth 
           -> FocusPhase     
           -> Ctxt (Assumption, Structure)    -- (unfocused) free variables
           -> Ctxt (Assumption, Structure)    
           -> Maybe Type
           -> Goal          
           -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure), Substitution, Bindings, Bool)
synthesiseInner defs resourceScheme inDef canDef depth focusPhase gamma omega grade goal@(Goal goalTySch@(Forall _ _ _ ty) structure) = do

  currentTime    <- liftIO $ Clock.getTime Clock.Monotonic
  state <- Synthesiser $ lift $ lift $ lift get
  Synthesiser $ lift $ lift $ lift $ modify (\state ->
            state {
                synDepthReached   = if not $ synDepthReached state   then synCurr depth >= synMax depth else True
              , elimDepthReached  = if not $ elimDepthReached state  then eCurr depth  >= eMax depth else True
             ,  introDepthReached = if not $ introDepthReached state then iCurr depth >= iMax depth else True
             ,  appDepthReached = if not $ appDepthReached state then appCurr depth >= appMax depth else True
                  })

  debugM "synthDebug - synthesiseInner with goal: " (show goal)
  debugM "synthDebug - synthesiseInner with gamma: " (show gamma)
  debugM "synthDebug - synthesiseInner with omega: " (show omega)
  debugM "synthDebug - synthesiseInner with focusPhase: " (show focusPhase)

  debugM "synthDebug - synthesiseInner with current e depth: " (show $ eCurr depth)
  debugM "synthDebug - synthesiseInner with current e max: " (show $ eMax depth)
  debugM "synthDebug - synthesiseInner with current i depth: " (show $ iCurr depth)
  debugM "synthDebug - synthesiseInner with current i max: " (show $ iMax depth)
  debugM "synthDebug - synthesiseInner with current app depth: " (show $ appCurr depth)
  debugM "synthDebug - synthesiseInner with current app max: " (show $ appMax depth)
  debugM "synthDebug - synthesiseInner with current syn depth: " (show $ synCurr depth)
  debugM "synthDebug - synthesiseInner with current syn max: " (show $ synMax depth)

  debugM "synthDebug - synthesiseInner with elim depth reached: " (show $ elimDepthReached state)
  debugM "synthDebug - synthesiseInner with intro depth reached: " (show $ introDepthReached state)
  debugM "synthDebug - synthesiseInner with syn depth reached: " (show $ synDepthReached state)
  debugM "synthDebug - synthesiseInner with app depth reached: " (show $ appDepthReached state)


  case (focusPhase, (synCurr depth < synMax depth) ) of -- &&  ((not $ (synDepthReached state && elimDepthReached state && introDepthReached state && appDepthReached state && defDepthReached state)))) of
      (Focus R Async, True) -> varHelper [] [] (gamma ++ omega) resourceScheme (Focus R Async) grade goal
                      `try`
                      absHelper defs gamma omega resourceScheme inDef canDef depth (Focus R Async) grade goal
                      `try`
                      rightAsyncTrans ty
      (Focus L Async, True) ->  
          -- varHelper [] [] (omega ++ gamma) resourceScheme (Focus L Async) grade goal
          -- `try`
          constrElimHelper defs gamma [] omega resourceScheme inDef canDef depth (Focus L Async) grade goal
          `try`
          unboxHelper defs gamma [] omega resourceScheme inDef canDef depth (Focus L Async) grade goal
          `try`
          leftAsyncTrans omega (eCurr depth >= eMax depth) (constructors state)
          `try`
          focusLeft [] gamma
          `try`
          focusRight ty omega 
      (Focus R Sync, True) ->
          varHelper [] [] gamma resourceScheme (Focus R Sync) grade goal
          `try`
          constrIntroHelper defs gamma resourceScheme inDef canDef depth (Focus R Sync) grade goal
          `try`
          boxHelper defs gamma resourceScheme inDef canDef depth (Focus R Sync) grade goal
          `try`
          blurRight goal 
      (Focus L Sync, True) -> 
            varHelper gamma [] omega resourceScheme (Focus L Sync) grade goal
            `try`
            appHelper defs gamma [] omega resourceScheme inDef canDef depth (Focus L Sync) grade goal
            `try`
            defHelper [] defs gamma omega resourceScheme inDef canDef depth (Focus L Sync) grade goal
            `try`
            blurLeft omega  (constructors state) (not $ appDepthReached state)
      (_, False) -> 
            varHelper [] [] (gamma ++ omega) resourceScheme (Focus L Sync) grade goal

  where 

    rightAsyncTrans (TyApp{}) = synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1}) (Focus L Async) gamma omega grade goal
    rightAsyncTrans (TyCon{}) = synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1}) (Focus L Async) gamma omega grade goal 
    rightAsyncTrans (Box{})   = synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1}) (Focus L Async) gamma omega grade goal
    rightAsyncTrans (TyVar{}) = synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1}) (Focus L Async) gamma omega grade goal
    rightAsyncTrans _ = none

    leftAsyncTrans [] _ _ = none
    leftAsyncTrans (assumption@(var, (tyA, structure)):omega') depthReached cons = 
      (case getAssumptionType tyA of 
        FunTy{} -> synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1}) (Focus L Async) (assumption:gamma) (omega') grade goal
        tyB ->  if isAtomic tyB || isZeroGrade tyA || structure == Decreasing || (isRecursiveType (isADTorGADT tyB) cons && depthReached) then  
                   synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1}) (Focus L Async) (assumption:gamma) (omega') grade goal
                else none)

    focusRight (TyApp{}) [] = synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1}) (Focus R Sync) gamma [] grade goal
    focusRight (TyCon{}) [] = synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1}) (Focus R Sync) gamma [] grade goal
    focusRight (Box{})   [] = synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1}) (Focus R Sync) gamma [] grade goal
    focusRight _ _ = none

    focusLeft _ [] = none
    focusLeft left (assumption:right) = 
      focusLeft (assumption : left) right
      `try`
      synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1}) (Focus L Sync) (left ++ right) (assumption:omega) grade goal

    blurRight (Goal (Forall _ _ _ FunTy{}) _)  =
      synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1 }) (Focus R Async) gamma omega grade goal
    blurRight (Goal (Forall _ _ _ TyVar{}) _) = 
      synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1 }) (Focus R Async) gamma omega grade goal
    blurRight (Goal (Forall _ _ _ TyApp{}) _) = 
      synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1 }) (Focus R Async) gamma omega grade goal
    blurRight (Goal (Forall _ _ _ TyCon{}) _) = 
      synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1 }) (Focus R Async) gamma omega grade goal
    blurRight _ = none
  
    blurLeft ((var@(_, (tyA, _))):omega) cons _ = 
      case (getAssumptionType tyA, isRecursiveType (isADTorGADT $ getAssumptionType tyA) cons) of 
        (TyApp{}, False) -> 
          synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1 }) (Focus L Async) gamma (var:omega) grade goal
        (TyCon{}, False) -> 
          synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1 }) (Focus L Async) gamma (var:omega) grade goal
        (Box{}, False) -> 
          synthesiseInner defs resourceScheme inDef canDef (depth { synCurr = (synCurr depth) + 1 }) (Focus L Async) gamma (var:omega) grade goal
        _ -> none
    blurLeft _ _ _ = none


synthesise :: (?globals :: Globals)
           => Ctxt TypeScheme
           -> ResourceScheme PruningScheme    -- whether the synthesis is in additive mode or not
           -> Ctxt (Assumption, Structure)    -- (unfocused) free variables
           -> Ctxt (Assumption, Structure)    -- focused variables
           -> Depth 
           -> Goal           -- type from which to synthesise
           -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure), Substitution)
synthesise defs resourceScheme gamma omega depth goal = do
  let gradeOnRule = fromMaybe False (globalsGradeOnRule ?globals)
  let initialGrade = if gradeOnRule then Just (TyGrade Nothing 1)  else Nothing


  st' <- get
  relevantConstructors <- do 
      let snd3 (a, b, c) = b
          tripleToTup (a, b, c) = (a, b)
      st <- get
      let pats = map (second snd3) (typeConstructors st)
      mapM (\ (a, b) -> do
          dc <- conv $ mapM (lookupDataConstructor nullSpanNoFile) b
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

  result@(expr, ctxt, subst, bindings, _) <- synthesiseInner defs resourceScheme False False depth (Focus R Async) gamma omega initialGrade goal

  case resourceScheme of
    Subtractive -> do
      -- All linear variables should be gone
      -- and all graded should approximate 0
      consumed <- mapM (\(id, (a, s)) ->
                    case a of
                      Linear{} -> return False;
                      Discharged _ grade -> do
                        (kind, _, _) <-  conv $ synthKind nullSpan grade
                        conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade kind)
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
                            conv $ addConstraint (ApproximatedBy nullSpanNoFile gradeUsed gradeSpec kind)
                            solve
                          _ -> return False
                      Nothing ->
                        case a of
                          Discharged _ gradeSpec -> do
                            (kind, _, _) <- conv $ synthKind nullSpan gradeSpec
                            conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) gradeSpec kind)
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
                      ,  synDepthReached = False
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
        
  let gamma' = map (\(v, a) -> (v, (a, None))) gamma

  -- Only use the defs that are specified in the hint (or all defs if this hint is specified)
  let defs' = if HUseAllDefs `elem` hints then defs 
              else case hasDefsHint hints of 
                        Just ids -> filter (\(id, _) -> id `elem` ids) defs
                        Nothing -> if HUseRec `elem` hints then filter (\(id, _) -> id `elem` (maybeToList currentDef)) defs else []



  result <- liftIO $ System.Timeout.timeout timeoutLim' $ loop (hintELim, hintILim) index defs' initialGrade gamma' 12 initialState
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
        let lims = runOmega $ liftM3 (,,) (each [0..elimMax]) (each [0..introMax]) (each [0..level])
        pRes <- foldM (\acc (elim, intro, app) -> 
          case acc of 
            (Just res, agg') -> return (Just res, agg')
            (Nothing, agg')  -> do 
              putStrLn $  "elim: " <> (show elim) <> " intro: " <> (show intro) <> " app: " <> (show app) <> " level: " <> (show level)  
              let synRes = synthesise defs resourceScheme gamma [] (Depth 0 elim 0 intro 0 app 0 level) grade (Goal goalTy NonDecreasing)
              (res, agg'') <- runStateT (runSynthesiser index synRes checkerState) (resetState agg')
              if (not $ solved res) && (depthReached agg'') then return (Nothing, agg'') else return (Just res, agg'')
          ) (Nothing, agg) lims
        case pRes of 
          (Just finRes, finAgg) -> return (finRes, finAgg)
          (Nothing, finAgg) -> loop (eHintMax, iHintMax) index defs grade gamma (level+1) finAgg 
 

      depthReached st = elimDepthReached st || introDepthReached st || appDepthReached st || synDepthReached st
      solved res = case res of ((Right (expr, _, _), _):_) -> True ; _ -> False
      resetState st = st { elimDepthReached = False, introDepthReached = False, synDepthReached = False}


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