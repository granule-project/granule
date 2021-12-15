{-# LANGUAGE ImplicitParams #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}


{-# options_ghc -fno-warn-incomplete-uni-patterns #-}
module Language.Granule.Synthesis.Synth where

--import Data.List
--import Control.Monad (forM_)
--import System.IO.Unsafe
import qualified Data.Map as M

import Data.List (sortBy)

import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
import Control.Monad.Logic
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span

import Language.Granule.Context

-- import Language.Granule.Checker.Checker
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
-- import Control.Monad.Except
--import Control.Monad.Trans.List
--import Control.Monad.Writer.Lazy
import Control.Monad.State.Strict

import qualified Control.Monad.State.Strict as State (get)
import qualified System.Clock as Clock

import Language.Granule.Utils
import Data.Maybe (fromJust, catMaybes, fromMaybe)
import Control.Arrow (second)
import System.Clock (TimeSpec)
-- import Language.Granule.Checker.Constraints.Compile (compileTypeConstraintToConstraint)
-- import Control.Monad.Trans.Except (runExceptT)
-- import Control.Monad.Error.Class


solve :: (?globals :: Globals)
  => Synthesiser Bool
solve = do
  cs <- conv State.get
  let pred = Conj $ predicateStack cs
  debugM "synthDebug" ("SMT on pred = " ++ pretty pred)
  tyVars <- conv $ includeOnlyGradeVariables nullSpanNoFile (tyVarContext cs)
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
    Timeout ->
      return False
    _ ->
      return False

-- * Context manipulations

ctxtSubtract :: (?globals :: Globals) => Ctxt (Assumption, Structure Id)  -> Ctxt (Assumption, Structure Id) -> Synthesiser (Ctxt (Assumption, Structure Id))
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
        conv $ existential var kind
        conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar var) g') g kind)
        -- maximality
        varOther' <- conv $ freshIdentifierBase "cOther"
        let varOther = mkId varOther'
        conv $ addPredicate (Impl [(varOther, kind)]
                                (Conj [Con $ ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar varOther) g') g kind])
                                (Conj [Con $ ApproximatedBy nullSpanNoFile (TyVar varOther) (TyVar var) kind]))
        return $ TyVar var

ctxtMultByCoeffect :: Type -> Ctxt (Assumption, Structure Id) -> Synthesiser (Ctxt (Assumption, Structure Id))
ctxtMultByCoeffect _ [] = return []
ctxtMultByCoeffect g1 ((x, (Discharged t g2, structure)):xs) = do
      ctxt <- ctxtMultByCoeffect g1 xs
      return ((x, (Discharged t (TyInfix TyOpTimes g1 g2), structure)): ctxt)
ctxtMultByCoeffect _ _ = none

ctxtDivByCoeffect :: (?globals :: Globals) => Type -> Ctxt (Assumption, Structure Id) -> Synthesiser (Ctxt (Assumption, Structure Id))
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
      conv $ existential var kind
      conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyInfix TyOpTimes g (TyVar var)) g' kind)
      return $ TyVar var
ctxtDivByCoeffect _ _ = none

ctxtMerge :: (?globals :: Globals)
          => (Type -> Type -> Type) -- lattice operator
          -> Ctxt (Assumption, Structure Id)
          -> Ctxt (Assumption, Structure Id)
          -> Synthesiser (Ctxt (Assumption, Structure Id))

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
ctxtMerge _ [] ((_, (Linear t, structure)) : ctxt) = none

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

ctxtAdd :: Ctxt (Assumption, Structure Id) -> Ctxt (Assumption, Structure Id) -> Maybe (Ctxt (Assumption, Structure Id))
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


-- * Focusing auxilliary functions

-- | Check if a type is Right Asynchronous (i.e. a function type)
isRAsync :: Type -> Bool
isRAsync FunTy {} = True
isRAsync _ = False

-- | Check if a type is Left Asynchronous (i.e. can it be decomposed)
isLAsync :: Type -> Bool
isLAsync ProdTy{} = True
isLAsync SumTy{} = True
isLAsync Box{} = True
isLAsync (TyCon (internalName -> "()")) = True
isLAsync (TyApp _ _) = True
isLAsync (TyCon _) = True
isLAsync _ = False

isAtomic :: Type -> Bool
isAtomic TyVar {} = True
isAtomic _ = False

isADT  :: Type -> Bool
isADT (TyCon _) = True
isADT (TyApp t _) = isADT t
isADT _ = False

adtName :: Type -> Maybe Id
adtName (TyCon id) = Just id
adtName (TyApp e1 e2) = adtName e1
adtName _ = Nothing

-- | Get the right most of a function type and collect its arguments in a list
rightMostFunTy :: Type -> (Type, [Type])
rightMostFunTy (FunTy _ arg t) = let (t', args) = rightMostFunTy t in (t', arg : args)
rightMostFunTy t = (t, [])

reconstructFunTy :: Type -> [Type] -> Type
reconstructFunTy = foldl (flip (FunTy Nothing))


data AltOrDefault = Default | Alternative
  deriving (Show, Eq)

data ResourceScheme a = Additive a | Subtractive a
  deriving (Show, Eq)

type Bindings = [(Id, (Id, Type))]

data Structure a = None | Arg a | Dec a
  deriving (Show, Eq)

bindToContext :: (Id, (Assumption, Structure Id)) -> Ctxt (Assumption, Structure Id) -> Ctxt (Assumption, Structure Id) -> Bool -> (Ctxt (Assumption, Structure Id), Ctxt (Assumption, Structure Id))
bindToContext var gamma omega True = (gamma, omega ++ [var])
bindToContext var gamma omega False = (gamma ++ [var], omega)

isDecreasing :: Structure Id -> Bool 
isDecreasing (Dec id) = True
isDecreasing _ = False

-- Note that the way this is used, the (var, assumption) pair in the first
-- argument is not contained in the provided context (second argument)
useVar :: (?globals :: Globals)
  => (Id, (Assumption, Structure Id))
  -> Ctxt (Assumption, Structure Id)
  -> ResourceScheme AltOrDefault
  -> Maybe Type -- Grade on rule style of synthesis 
  -> Synthesiser (Bool, Ctxt (Assumption, Structure Id), Type)
-- Subtractive
useVar (name, (Linear t, _)) gamma Subtractive{} _ = return (True, gamma, t)
useVar (name, (Discharged t grade, structure)) gamma Subtractive{} Nothing = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  var <- conv $ freshTyVarInContext (mkId "c") kind
  conv $ existential var kind
  -- conv $ addPredicate (Impl [] (Con (Neq nullSpanNoFile (CZero kind) grade kind))
  --                              (Con (ApproximatedBy nullSpanNoFile (CPlus (TyVar var) (COne kind)) grade kind)))
  conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar var) (TyGrade (Just kind) 1)) grade kind)
  res <- solve
  if res then
    return (True, replace gamma name (Discharged t (TyVar var), structure), t) else
    return (False, [], t)
useVar (name, (Discharged t grade, structure)) gamma Subtractive{} (Just grade') = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  var <- conv $ freshTyVarInContext (mkId "c") kind
  conv $ existential var kind
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
  => Ctxt (Assumption, Structure Id)
  -> Ctxt (Assumption, Structure Id)
  -> ResourceScheme AltOrDefault
  -> Maybe Type
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure Id), Substitution, Bindings, Bool)
varHelper left [] _ _ _ = none
varHelper left (var@(x, (a, s)) : right) resourceScheme grade goalTy@(Forall _ binders constraints goalTy') =
 varHelper (var:left) right resourceScheme grade goalTy `try`
   (do
      conv $ resetAddedConstraintsFlag -- reset the flag that says if any constraints were added
      (success, specTy, subst) <- conv $ equalTypes nullSpanNoFile (getAssumptionType a) goalTy'
      if success then do
          -- see if any constraints were added
          st <- conv $ get
          solved <- if addedConstraints st
                      then solve
                      else return True
          -- now to do check we can actually use it
          if solved then do
              (canUse, gamma, t) <- useVar var (left ++ right) resourceScheme grade
              boolToSynthesiser canUse (makeVar x goalTy, gamma, subst, [], isDecreasing s)
            else
              none
      else none)


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
  => Ctxt Type
  -> Bool
  -> Ctxt (Assumption, Structure Id)
  -> Ctxt (Assumption, Structure Id)
  -> ResourceScheme AltOrDefault
  -> Maybe Type
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure Id), Substitution, Bindings, Bool)
absHelper defs allowRSync gamma omega resourceScheme grade goalTy@(Forall _ binders constraints (FunTy name t1 t2)) = do
    -- Fresh var
    id <- useBinderNameOrFreshen name
    state <- Synthesiser $ lift $ lift $ lift get
    -- Build recursive context depending on focus mode
    let (gamma', omega') =
          if isLAsync t1 then
            (gamma, (id, (Linear t1, Arg (topLevelDef state))):omega)
          else
            ((id, (Linear t1, None)):gamma, omega)

    -- Synthesis body
    debugM "synthDebug" $ "Lambda-binding " ++ pretty [(id, Linear t1)]
    (e, delta, subst, bindings, sd) <- synthesiseInner defs False resourceScheme gamma' omega' grade (Forall nullSpanNoFile binders constraints t2) (True, allowRSync, False)
    debugM "synthDebug" $ "Made a lambda: " ++ pretty (makeAbs id e goalTy)


    -- Check resource use at the end
    case (resourceScheme, lookupAndCutout id delta) of
      (Additive{}, Just (delta', (Linear _, _))) ->
        return (makeAbs id e goalTy, delta', subst, bindings, sd)
      (Subtractive{}, Nothing) ->
        return (makeAbs id e goalTy, delta, subst, bindings, sd)
      _ ->
        none
absHelper _ _ _ _ _ _ _ = none


appHelper :: (?globals :: Globals)
  => (Bool, Bool)
  -> Ctxt Type
  -> Ctxt (Assumption, Structure Id)
  -> Ctxt (Assumption, Structure Id)
  -> ResourceScheme AltOrDefault
  -> Maybe Type
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure Id), Substitution, Bindings, Bool)
appHelper _ _ left [] _ _ _ = none

{-
Subtractive

x2 ∉ Δ1
Γ, x2 : B ⊢ C ⇒ t1 ; Δ1
Δ1 ⊢ A ⇒ t2 ; Δ2
------------------------ :: app
Γ, x1 : A → B ⊢ C ⇒ [(x1 t2) / x2] t1 ; Δ2

-}
appHelper (allowRSync, allowDef) defs left (var@(x, (a, s)) : right) sub@Subtractive{} grade goalTy@(Forall _ binders constraints _ ) =
  appHelper (allowRSync, allowDef) defs (var : left) right sub grade goalTy `try`
  (case getAssumptionType a of
    (FunTy _ t1 t2) -> do
      debugM "synthDebug" ("Trying to use a function " ++ show var ++ " to get goal " ++ pretty goalTy)

      let omega = left ++ right
      (canUse, omega', t) <- useVar var omega sub grade
      if canUse
        then do
          id <- freshIdentifier
          let (gamma', omega'') = bindToContext (id, (Linear t2, None)) omega' [] (isLAsync t2)

          debugM "synthDebug" ("Inside app, try to synth the goal " ++ pretty goalTy ++ " under context of " ++ pretty [(id, Linear t2)])
          (e1, delta1, sub1, bindings1, sd1) <- synthesiseInner defs False sub gamma' omega'' grade goalTy (False, allowRSync, False)
          case lookup id delta1 of
            Nothing -> do
              -- Check that `id` was used by `e1` (and thus is not in `delta1`)
              debugM "synthDebug" ("Inside app, try to synth the argument at type " ++ pretty t1)
              (e2, delta2, sub2, bindings2, sd2) <- synthesiseInner defs False sub delta1 [] grade (Forall nullSpanNoFile binders constraints t1) (False, allowRSync, False)
              debugM "synthDebug" ("Inside app, made a " ++ (pretty $ Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy t) id e1 ))
              subst <- conv $ combineSubstitutions nullSpanNoFile sub1 sub2
              return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy t) id e1, delta2, subst, bindings1 ++ bindings2, sd1 || sd2)
            _ -> none
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
appHelper (allowRSync, allowDef) defs left (var@(x, (a, s)) : right) add@(Additive mode) grade goalTy@(Forall _ binders constraints _ ) =
  appHelper (allowRSync, allowDef) defs (var : left) right add grade goalTy `try`
  (case getAssumptionType a of
    (FunTy _ tyA tyB) -> do
      let omega = left ++ right
      (canUse, useContextOut, _) <- useVar var omega add grade
      if canUse
        then do
          x2 <- freshIdentifier
          -- Extend context (focussed) with x2 : B

          let (gamma', omega') = bindToContext (x2, (Linear tyB, None)) omega [] (isLAsync tyB)
          -- Synthesise new goal binding result `x2`
          (e1, delta1, sub1, bindings1, sd1) <- synthesiseInner defs False add gamma' omega' grade goalTy (False, allowRSync, False)
          -- Make sure that `x2` appears in the result
          case lookupAndCutout x2 delta1 of
            Just (delta1',  (Linear _, _)) -> do
              -- Pruning subtraction

              gamma2 <-
                case mode of
                  Default     -> return omega
                  Alternative -> ctxtSubtract (gamma' ++ omega') delta1'

              -- Synthesise the argument
              (e2, delta2, sub2, bindings2, sd2) <- synthesiseInner defs False add gamma2 [] grade (Forall nullSpanNoFile binders constraints tyA) (False, allowRSync, False)

              -- Add the results
              deltaOut <- maybeToSynthesiser $ ctxtAdd useContextOut delta1'
              deltaOut' <- maybeToSynthesiser $ ctxtAdd deltaOut delta2

              subst <- conv $ combineSubstitutions nullSpan sub1 sub2
              debugM "synthDebug" ("Inside app, made a " ++ (pretty $ Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy tyA) x2 e1 ))
              return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy tyA) x2 e1, deltaOut', subst, bindings1 ++ bindings2, sd1 || sd2)
            _ -> none
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
  => Ctxt Type
  -> Ctxt (Assumption, Structure Id)
  -> ResourceScheme AltOrDefault
  -> Maybe Type
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure Id), Substitution, Bindings, Bool)
boxHelper defs gamma resourceScheme grade goalTy =
  case goalTy of
    (Forall _ binders constraints (Box g t)) ->
      let newGrade = case grade of
              Just grade' -> Just $ TyInfix TyOpTimes grade' g
              Nothing -> Nothing
      in
      case resourceScheme of
        Additive{} -> do
            (e, delta, subst, bindings, sd) <- synthesiseInner defs False resourceScheme gamma [] newGrade (Forall nullSpanNoFile binders constraints t) (False, True, False)
            deltaOut <- case newGrade of
                  Just _ -> return delta
                  Nothing -> ctxtMultByCoeffect g delta
            return (makeBox goalTy e, deltaOut, subst, bindings, sd)
        Subtractive Default -> do
            (e, delta, subst, bindings, sd) <- synthesiseInner defs False resourceScheme gamma [] newGrade (Forall nullSpanNoFile binders constraints t) (False, True, False)
            deltaOut <- case newGrade of
                  Just _ -> return delta
                  Nothing -> do
                    used <- ctxtSubtract gamma delta
                    -- Compute what was used to synth e
                    delta' <- ctxtMultByCoeffect g used
                    ctxtSubtract gamma delta'
            res <- solve
            boolToSynthesiser res (makeBox goalTy e, deltaOut, subst, bindings, sd)
        Subtractive Alternative -> do
          gamma' <- ctxtDivByCoeffect g gamma
          (e, delta, subst, bindings, sd) <- synthesiseInner defs False resourceScheme gamma' [] newGrade (Forall nullSpanNoFile binders constraints t) (False, True, False)
          delta' <- ctxtMultByCoeffect g delta
          res <- solve
          boolToSynthesiser res (makeBox goalTy e, delta', subst, bindings, sd)
    _ -> none


unboxHelper :: (?globals :: Globals)
  => Ctxt Type
  -> Ctxt (Assumption, Structure Id)
  -> Ctxt (Assumption, Structure Id)
  -> Ctxt (Assumption, Structure Id)
  -> ResourceScheme AltOrDefault
  -> Maybe Type
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure Id), Substitution, Bindings, Bool)
unboxHelper _ left [] _ _ _ _ = none

{-
Subtractive
0 <= s
Γ, x2 : [A] r ⊢ B ⇒ e ; Δ, x2 : [A] s
-------------------------------------------- :: unbox
Γ, x1 : [] r A ⊢ B ⇒ let [x2] = x1 in e; Δ

-}

unboxHelper defs left (var@(x1, (a, structure)) : right) gamma sub@Subtractive{} grade goalTy =
  unboxHelper defs (var : left) right gamma sub grade goalTy `try`
    (case a of
      Linear (Box grade_r tyA) -> do
        debugM "synthDebug" $ "Trying to unbox " ++ pretty a

        let omega = left ++ right
        (canUse, omega', _) <- useVar var omega sub grade
        if canUse then do
          --
          x2 <- freshIdentifier
          let (gamma', omega'') = bindToContext (x2, (Discharged tyA grade_r, structure)) gamma omega' (isLAsync tyA)
          -- Synthesise inner
          debugM "synthDebug" $ "Inside unboxing try to synth for " ++ pretty goalTy ++ " under " ++ pretty [(x2, Discharged tyA grade_r)]
          (e, delta, subst, bindings, sd) <- synthesiseInner defs False sub gamma' omega'' grade goalTy (True, True, False)
          ---
          case lookupAndCutout x2 delta of
            Just (delta', (Discharged _ grade_s, _)) -> do
              -- Check that: 0 <= s
              (kind, _, _) <- conv $ synthKind nullSpan grade_s
              conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade_s kind)
              res <- solve
              -- If we succeed, create the let binding
              debugM "made aaaa: " (pretty $ makeUnbox x2 x1 goalTy (Box grade_r tyA) tyA e)
              boolToSynthesiser res (makeUnbox x2 x1 goalTy (Box grade_r tyA) tyA e, delta', subst, (x1, (x2, Box grade_r tyA)):bindings, sd)

            _ -> none
        else none
      Discharged (Box grade_r tyA) grade_s -> do
        debugM "I'm trying a double unboxing with "  (show grade_r)
        let omega = left ++ right
        (canUse, omega', _) <- useVar var omega sub grade 
        debugM "in a double unboxing canUse: " (show canUse)
        if canUse then do 
          y <- freshIdentifier
          let (gamma', omega'') = bindToContext (y, (Discharged tyA (TyInfix TyOpTimes grade_r grade_s), structure)) gamma omega' (isLAsync tyA)
          debugM "in a double unboxing binding " (pretty y <> " : " <> pretty (Discharged tyA (TyInfix TyOpTimes grade_r grade_s)))
          debugM "in a double unboxing trying to synth for " (pretty goalTy <> " with contexts gamma: " <> show gamma' <> " and omega: " <> show omega'') 
          (e, delta, subst, bindings, sd) <- synthesiseInner defs False sub gamma' omega'' grade goalTy (True, True, False)
          debugM "in a double unboxing making a " (pretty e <> " with output context delta: " <> show delta) 
          case lookupAndCutout y delta of
            Just (delta', (Discharged _ grade_s', _)) ->  do 
              (kind, _, _) <- conv $ synthKind nullSpan grade_s'
              r' <- conv $ freshTyVarInContext (mkId "r'") kind
              conv $ existential r' kind
              conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyInfix TyOpTimes (TyVar r') grade_s) grade_s' kind)
              res <- solve 
              boolToSynthesiser res (makeUnbox y x1 goalTy (Box grade_r tyA) tyA e, replace delta' x1 (Discharged (Box grade_r tyA) (TyVar r'), structure), subst, (x1, (y, Box grade_r tyA)):bindings, sd)
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
unboxHelper defs left (var@(x, (a, structure)) : right) gamma add@(Additive mode) ruleGrade goalTy =
  unboxHelper defs (var : left) right gamma add ruleGrade goalTy `try`
   (case a of
     (Linear (Box grade t')) -> do
       let omega = left ++ right
       (canUse, omega', t) <- useVar var omega add ruleGrade
       if canUse
          then do
            x2 <- freshIdentifier
            -- omega1 <- ctxtSubtract omega omega'
            let (gamma', omega'') = bindToContext (x2, (Discharged t' grade, structure)) gamma omega (isLAsync t')

            -- Synthesise the body of a `let` unboxing
            (e, delta, subst, bindings, sd) <- synthesiseInner defs False add gamma' omega'' ruleGrade goalTy (True, True, False)

            -- Add usage at the binder to the usage in the body
            delta' <- maybeToSynthesiser $ ctxtAdd omega' delta

            case lookupAndCutout x2 delta' of
              Just (delta'', (Discharged _ usage, _)) -> do
                (kind, _, _) <- conv $ synthKind nullSpan grade

                debugM "check" (pretty usage ++ " <=? " ++ pretty grade)
                conv $ addConstraint (ApproximatedBy nullSpanNoFile usage grade kind)
                res <- solve
                if res then
                  return (makeUnbox x2 x goalTy t' (Box grade t') e,  delta'', subst, (x, (x2, Box grade t')):bindings, sd) else none
              _ -> do
                (kind, _, _) <- conv $ synthKind nullSpan grade
                conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade kind)
                res <- solve
                if res then
                  return (makeUnbox x2 x goalTy t' (Box grade t') e,  delta', subst, (x, (x2, Box grade t')):bindings, sd) else none
          else none
     _ -> none)



constrIntroHelper :: (?globals :: Globals)
  => (Bool, Bool)
  -> Ctxt Type
  -> Ctxt (Assumption, Structure Id)
  -> ResourceScheme AltOrDefault
  -> Maybe Type
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure Id), Substitution, Bindings, Bool)
constrIntroHelper (True, allowDef) defs gamma mode grade goalTy@(Forall s binders constraints t) =
  case (isADT t, adtName t) of
    (True, Just name) -> do
      debugM "Entered constrIntro helper with goal: " (show goalTy)

      state <- Synthesiser $ lift $ lift $ get

      -- Retrieve the data constructors for the goal data type
      let adtConstructors = concatMap snd (filter (\x -> fst x == name) (constructors state))

      -- For each relevent data constructor, we must now check that it's type matches the goal
      adtConstructors' <- foldM (\ a (id, (conTy@(Forall s binders constraints conTy'), subst)) -> do
         (success, specTy, specSubst) <- checkConstructor conTy subst
         case (success, specTy) of
           (True, Just specTy') -> do
             subst' <- conv $ combineSubstitutions s subst specSubst
             specTy'' <- conv $ substitute subst' specTy'
             return $ (id, (Forall s binders constraints specTy'', subst')) : a
           _ -> return a ) [] adtConstructors

      -- Attempt to synthesise each applicable constructor, in order of ascending arity
      synthesiseConstructors gamma (sortBy (flip compare') adtConstructors') mode goalTy
    _ -> none
  where


    compare' con1@(_, (Forall _ _ _ ty1, _)) con2@(_, (Forall _ _ _ ty2, _)) = compare (arity ty1) (arity ty2)

    -- | Given a data constructor and a substition of type indexes, check that the goal type ~ data constructor type
    checkConstructor :: TypeScheme -> Substitution -> Synthesiser (Bool, Maybe Type, Substitution)
    checkConstructor con@(Forall _ binders coercions conTy) subst = do
      (result, local) <- conv $ peekChecker $ do

        (conTyFresh, tyVarsFreshD, substFromFreshening, constraints, coercions') <- freshPolymorphicInstance InstanceQ False con subst []

        -- Take the rightmost type of the function type, collecting the arguments along the way 
        let (conTy'', args) = rightMostFunTy conTyFresh

        conTy'' <- substitute coercions' conTy''

        (success, spec, subst') <- equalTypes nullSpanNoFile t conTy''


        cs <- get
        -- Run the solver (i.e. to check constraints on type indexes hold)
        result <-
          if addedConstraints cs then do
            let predicate = Conj $ predicateStack cs
            predicate <- substitute subst' predicate

            debugM "pred: " (pretty predicate)
            let ctxtCk  = tyVarContext cs
            coeffectVars <- includeOnlyGradeVariables s ctxtCk
            coeffectVars <- return (coeffectVars `deleteVars` Language.Granule.Checker.Predicates.boundVars predicate)
            constructors <- allDataConstructorNames
            (_, result) <- liftIO $ provePredicate predicate coeffectVars constructors
            return result
          else return QED

        case result of
          QED -> do -- If the solver succeeds, return the specialised type
            spec <- substitute substFromFreshening spec
            return (success, Just $ reconstructFunTy spec (reverse args), subst')
          _ ->
            return (False, Nothing, [])
      case result of
        Right (success, Just spec, subst') -> conv $ local >> return (success, Just spec, subst')
        _ -> return (False, Nothing, [])


    -- Traverse the constructor types and attempt to synthesise a program for each one
    synthesiseConstructors gamma [] mode goalTy = none
    synthesiseConstructors gamma ((id, (Forall s binders' constraints' ty, subst)):cons) mode goalTy =
      case constrArgs ty of
        -- If the constructor type has no arguments, then it is a nullary constructor and we can simply return the introduction form
        Just [] -> do
          let delta = case mode of
                Additive{} -> []
                Subtractive{} -> gamma
          return (makeNullaryConstructor id, delta, subst, [], False)
          `try` synthesiseConstructors gamma cons mode goalTy
        -- If the constructor has 1 or more arguments then we must synthesise each argument in turn
        Just args -> do
          (exprs, delta, subst', bindings, sd) <- synthConstructorArgs args binders' constraints' gamma mode subst
          return (makeConstr exprs id ty, delta, subst', bindings, sd)
          `try` synthesiseConstructors gamma cons mode goalTy
        Nothing ->
          none

    -- Traverse the argument types to the constructor and synthesise a term for each one
    synthConstructorArgs [t'] bs cs gamma mode constrSubst = do
      (es, deltas, subst, bindings, sd) <- synthesiseInner defs False mode gamma [] grade (Forall s bs cs t') (True, True, allowDef)
      subst' <- conv $ combineSubstitutions nullSpanNoFile constrSubst subst
      return ([(es, t')], deltas, subst', bindings, sd)
    synthConstructorArgs (t':ts) bs cs gamma mode constrSubst = do
      (es, deltas, subst, bindings, sd) <- synthConstructorArgs ts bs cs gamma mode constrSubst
      subst' <- conv $ combineSubstitutions nullSpanNoFile constrSubst subst
      gamma2 <- case mode of
            Additive Default -> return gamma
            Additive Alternative -> ctxtSubtract gamma deltas -- Pruning
            Subtractive{} -> return deltas
      (e2, delta2, subst2, bindings2, sd2) <- synthesiseInner defs False mode gamma2 [] grade (Forall s bs cs t') (True, True, allowDef)
      subst'' <- conv $ combineSubstitutions nullSpanNoFile subst2 subst'
      delta3 <- case mode of
            Additive{} -> maybeToSynthesiser $ ctxtAdd deltas delta2
            Subtractive{} -> return delta2
      return ((e2, t'):es, delta3, subst'', bindings ++ bindings2, sd || sd2)
    synthConstructorArgs _ _ _ _ _ _ = none

    constrArgs (TyCon _) = Just []
    constrArgs (TyApp _ _) = Just []
    constrArgs (FunTy _ e1 e2) = do
      res <- constrArgs e2
      return $ e1 : res
    constrArgs _ = Nothing


constrIntroHelper (_, allowDef) defs gamma mode _ goalTy@(Forall s binders constraints t) = none

constrElimHelper :: (?globals :: Globals)
  => (Bool, Bool)
  -> Ctxt Type
  -> Ctxt (Assumption, Structure Id)
  -> Ctxt (Assumption, Structure Id)
  -> Ctxt (Assumption, Structure Id)
  -> ResourceScheme AltOrDefault
  -> Maybe Type
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure Id), Substitution, Bindings, Bool)
constrElimHelper (allowRSync, allowDef) defs left [] _ _ _ _ = none
constrElimHelper (allowRSync, allowDef) defs left (var@(x, (a, structure)):right) gamma mode grade goalTySch@(Forall _ _ _ goalTy) =
  constrElimHelper (allowRSync, allowDef) defs (var:left) right gamma mode grade goalTySch `try` do
    debugM "in constr elim" ""
    let omega = left ++ right
    (canUse, omega', _) <- useVar var omega mode grade
    state <- Synthesiser $ lift $ lift $ lift get
    let topLevelDefId = topLevelDef state
    let (assumptionTy, grade) = case a of
          Linear t -> (t, Nothing)
          Discharged t g -> (t, Just g)
    if canUse && isADT assumptionTy then
      case adtName assumptionTy of
        Just name -> do
        -- (_, cases) <- conv $ generateCases nullSpanNoFile constructors [var] [x] (Just $ FunTy Nothing t goalTy)
        -- (_, cases) <- conv $ generateCases nullSpanNoFile (constructors state) [(x, Linear (Box grade t))] [x] (Just $ FunTy Nothing (Box grade t) goalTy)
          let adtConstructors = concatMap snd (filter (\x -> fst x == name) (constructors state))
          -- For each relevent data constructor, we must now check that it's type matches the goal
          cases <- foldM (\ a (id, (conTy@(Forall s binders constraints conTy'), subst)) -> do
            (success, (pat, assumptions, subst')) <- checkConstructor id topLevelDefId conTy assumptionTy subst grade
            case (success, pat) of
              (True, Just pat) -> do
                subst'' <- conv $ combineSubstitutions s subst subst'
                return $ (pat, assumptions, subst'') : a
              _ -> return a) [] adtConstructors
          debugM "linear cases: " (show cases <> " assumption ty: " <> show assumptionTy)
          case (mode, grade) of
            (Subtractive{}, Nothing) -> do
              (patterns, delta, subst, bindings', sd) <- synthCases assumptionTy mode gamma omega' cases goalTySch
              return (makeCase' assumptionTy x patterns goalTy, delta, subst, bindings', sd)
            (Additive{}, Nothing) -> do
              (patterns, delta, subst, bindings', sd) <- synthCases assumptionTy mode gamma omega cases goalTySch
              delta2 <- maybeToSynthesiser $ ctxtAdd omega' delta
              return (makeCase' assumptionTy x patterns goalTy, delta2, subst, bindings', sd)
            (Subtractive{}, Just grade') -> do
              let omega'' = deleteVar x omega'
              (patterns, delta, subst, bindings', sd) <- synthCases assumptionTy mode gamma omega'' cases goalTySch
              -- return (makeBoxCase assumptionTy grade' x patterns goalTy, omega' ++ delta, subst, bindings')
              return (makeBoxCase assumptionTy grade' x patterns goalTy, delta, subst, bindings', sd)
            (Additive{}, Just grade') -> do
              (patterns, delta, subst, bindings', sd) <- synthCases assumptionTy mode gamma omega cases goalTySch
              return (makeBoxCase assumptionTy grade' x patterns goalTy, delta, subst, bindings', sd)
        _ -> none
    else none

  where

    checkConstructor :: Id -> Id -> TypeScheme -> Type -> Substitution -> Maybe Type -> Synthesiser (Bool, (Maybe (Pattern ()), Ctxt (Assumption, Structure Id), Substitution))
    checkConstructor name topLevelDef con@(Forall  _ binders constraints conTy) assumptionTy subst grade = do
      (result, local) <- conv $ peekChecker $ do

        (conTyFresh, tyVarsFreshD, substFromFreshening, constraints, coercions') <- freshPolymorphicInstance InstanceQ False con subst []

        -- Take the rightmost type of the function type, collecting the arguments along the way 
        let (conTy'', args) = rightMostFunTy conTyFresh

        conTy'' <- substitute coercions' conTy''

        (success, spec, subst') <- equalTypes nullSpanNoFile assumptionTy conTy''

        cs <- get

        -- Run the solver (i.e. to check constraints on type indexes hold)
        result <-
          if addedConstraints cs then do
            let predicate = Conj $ predicateStack cs
            predicate <- substitute subst' predicate

            debugM "pred: " (pretty predicate)
            let ctxtCk  = tyVarContext cs
            coeffectVars <- includeOnlyGradeVariables nullSpanNoFile ctxtCk
            coeffectVars <- return (coeffectVars `deleteVars` Language.Granule.Checker.Predicates.boundVars predicate)
            constructors <- allDataConstructorNames
            (_, result) <- liftIO $ provePredicate predicate coeffectVars constructors
            return result
          else return QED

        case result of
          QED -> do -- If the solver succeeds, return the specialised type
            debugM "success!" (show name)
            spec <- substitute substFromFreshening spec

            -- Construct pattern based on constructor arguments specialised by type equality
            assmps <- mapM (\ arg -> do
              var <- freshIdentifierBase "x"
              arg' <- substitute subst' arg

        
              (structure, local) <- peekChecker $ do
                (success, spec, subst') <- equalTypes nullSpanNoFile arg' assumptionTy
                if success then return $ Dec topLevelDef else return $ Arg topLevelDef

              let annotation = case structure of 
                    Right struct -> struct
                    Left _ -> Arg topLevelDef
              
            --  let structure' = case structure of
            --        (Right struct, _) -> struct
            --        (Left _, _) -> Arg topLevelDef

              let assumption = case grade of
                    Nothing -> (Linear arg', annotation)
                    Just grade' -> (Discharged arg' grade', annotation)


              debugM "constrElim assumption: " (show assumption)
              return (mkId $ removeDots var, assumption, success)) args

            let (vars, assmps', recursiveArgs) = unzip3 assmps
            let assmps'' = zip vars assmps'


            let structDecr = or recursiveArgs

            let pat = makePattern name vars grade

            return (success, structDecr, (Just pat, assmps'', subst'))
          _ ->
            return (False, False, (Nothing, [], []))
      case result of
        Right (True, structDecr, (pat, assmps, subst)) -> do 
          
          Synthesiser $ lift $ lift $ lift $ modify (\state ->
              state {
                structurallyDecreasing = structDecr
                  })
          conv $ local >> return (True, (pat, assmps, subst))
        _ -> return (False, (Nothing, [], []))

    removeDots xs =  [ x | x <- xs, x `notElem` "." ]

    makePattern conId vars Nothing = PConstr nullSpanNoFile () False conId (map (PVar nullSpanNoFile () False) vars)
    makePattern conId vars (Just grade) = PBox nullSpanNoFile () False (PConstr nullSpanNoFile () False conId (map (PVar nullSpanNoFile () False) vars))

    synthCases adt mode g o [(p, assmps, conSubst)] goalTy = do
      let (g', o', unboxed) = bindAssumptions assmps g o []
      (e, delta, subst, bindings, sd1) <- synthesiseInner defs False mode g' o' grade goalTy (False, True, True)
      debugM "in synth next cases - \n goal: " (show goalTy <> " \n e: " <> pretty e <> " \n delta: "  <> show delta ++ "\n g': " ++ show g' ++ "\n o': " ++ show o' ++ "\n p: " ++ show p ++ "\n asmps: " ++ show assmps)
      del' <- checkAssumptions (x, getAssumptionType a) mode delta assmps unboxed
      case transformPattern bindings adt (g' ++ o') p unboxed of
        Just (pat, bindings') -> do
          return ([(pat, e)], del', subst, bindings', sd1)
        Nothing -> none

    synthCases adt mode g o ((p, assmps, conSubst):cons) goalTy = do
      (exprs, delta, subst, bindings, sd) <- synthCases adt mode g o cons goalTy
      let (g', o', unboxed) = bindAssumptions assmps g o []
      (e, delta', subst', bindings', sd') <- synthesiseInner defs False mode g' o' grade goalTy (False, True, True)
      debugM "in synth cases: " (show e <> " " <> show delta' ++ "g': " ++ show g' ++ " o': " ++ show o' ++ "p: " ++ show p ++ " asmps: " ++ show assmps)
      del' <- checkAssumptions (x, getAssumptionType a) mode delta' assmps unboxed
      case transformPattern bindings' adt (g' ++ o') p unboxed of
        Just (pat, bindings'') ->
          let op = case mode of Additive{} -> TyInfix TyOpJoin ; _ -> TyInfix TyOpMeet
          in do
            returnDelta <- ctxtMerge op del' delta
            returnSubst <- conv $ combineSubstitutions nullSpanNoFile subst subst'
            return ((pat, e):exprs, returnDelta, returnSubst, bindings ++ bindings'', sd || sd')
        Nothing -> none
    synthCases adt mode g o _ goalTy = none


checkAssumptions :: (?globals::Globals) => (Id, Type)
  -> ResourceScheme a
  -> [(Id, (Assumption, Structure Id))]
  -> [(Id, (Assumption, Structure Id))]
  -> Ctxt (Assumption, Structure Id) -> Synthesiser [(Id, (Assumption, Structure Id))]
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
checkAssumptions (x, t') sub@Additive{} del ((id, (Discharged t g, structure)):assmps) unboxed = do
      case lookupAndCutout id del of
        Just (del', (Discharged _ g', structure)) ->
          case lookup id unboxed of
            Just (Discharged _ g'', structure) -> do
              del'' <- checkAssumptions (x, t') sub del' assmps unboxed
              (kind, _, _) <- conv $ synthKind nullSpan g'
              conv $ addConstraint (ApproximatedBy nullSpanNoFile g' g'' kind)
              res <- solve
              if res then do
                ctxtMerge (TyInfix TyOpJoin) [(x, (Discharged t' g, structure))] del''
              else none
            _ -> (do
              del'' <- checkAssumptions (x, t') sub del' assmps unboxed
              (kind, _, _) <- conv $ synthKind nullSpan g'
              conv $ addConstraint (ApproximatedBy nullSpanNoFile g' g kind)
              res <- solve
              if res then do
               ctxtMerge (TyInfix TyOpJoin) [(x, (Discharged t' g', structure))] del''
              else none)
        _ -> do
          (kind, _, _) <- conv $ synthKind nullSpan g
          conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) g kind)
          res <- solve
          if res then checkAssumptions (x, t') sub del assmps unboxed else none

bindAssumptions ::
  [(Id, (Assumption, Structure Id))]
  -> Ctxt (Assumption, Structure Id)
  -> Ctxt (Assumption, Structure Id)
  -> Ctxt (Assumption, Structure Id)
  -> (Ctxt (Assumption, Structure Id), Ctxt (Assumption, Structure Id), Ctxt (Assumption, Structure Id))
bindAssumptions [] g o unboxed = (g, o, unboxed)
bindAssumptions (assumption@(id, (Linear t, structure)):assmps) g o unboxed =
  let (g', o') = bindToContext assumption g o (isLAsync t) in
  bindAssumptions assmps g' o'  unboxed
bindAssumptions (assumption@(id, (Discharged (Box grade t) grade', structure)):assmps) g o unboxed =
  let (g', o') = bindToContext (id, (Discharged t (TyInfix TyOpTimes grade grade'), structure)) g o (isLAsync t) in
  bindAssumptions assmps g' o' ((id, (Discharged t (TyInfix TyOpTimes grade grade'), structure)):unboxed)
bindAssumptions (assumption@(id, (Discharged t _, structure)):assmps) g o unboxed =
  let (g', o') = bindToContext assumption g o (isLAsync t) in
  bindAssumptions assmps g' o' unboxed


-- Construct a typed pattern from an untyped one from the context
transformPattern :: Ctxt (Id, Type) -> Type -> [(Id, (Assumption, Structure Id))] -> Pattern () -> Ctxt (Assumption, Structure Id) -> Maybe (Pattern Type, Ctxt (Id, Type))
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

transformPatterns :: Ctxt (Id, Type) -> Type -> [(Id, (Assumption, Structure Id))] -> [Pattern ()] -> Ctxt (Assumption, Structure Id) -> Maybe ([Pattern Type], Ctxt (Id, Type))
transformPatterns bindings adt ctxt [] unboxed = Just ([], bindings)
transformPatterns bindings adt ctxt (p:ps) unboxed = do
  (pat, bindings') <- transformPattern bindings adt ctxt p unboxed
  (res, bindingsFinal) <- transformPatterns bindings' adt ctxt ps unboxed
  return (pat:res, bindingsFinal)




linearVars :: Ctxt (Assumption, Structure Id) -> Ctxt (Assumption, Structure Id)
linearVars (var@(x, (Linear a, structure)):xs) = var : linearVars xs
linearVars ((x, (Discharged{}, structure)):xs) = linearVars xs
linearVars [] = []



defHelper :: (?globals :: Globals)
  => Ctxt Type
  -> Ctxt Type
  -> Ctxt (Assumption, Structure Id)
  -> ResourceScheme AltOrDefault
  -> Maybe Type
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure Id), Substitution, Bindings, Bool)
defHelper left [] _ _ _ _ = none

defHelper left (def@(x, t):right) gamma  sub@Subtractive{} grade goalTy@(Forall _ binders constraints _ ) =
 defHelper (def:left) right gamma sub grade goalTy `try`
  (case t of
    (FunTy _ t1 t2) -> do
      debugM "entered def helper t: " (show t ++ "goal: " <> show goalTy <> "gamma: " <> show gamma)
      id <- freshIdentifier
      let (gamma', omega') = bindToContext (id, (Linear t2, None)) gamma [] (isLAsync t2)
      (e1, delta1, sub1, bindings1, sd1) <- synthesiseInner (left++right) False sub gamma' omega' grade goalTy (False, False, False)
      debugM "defhelper made a: " (pretty e1)
      case lookup id delta1 of
        Nothing -> do
          (e2, delta2, sub2, bindings2, sd2) <- synthesiseInner (left++right) False sub delta1 [] grade (Forall nullSpanNoFile binders constraints t1) (False, False, False)
          if sd2 then do 
            debugM "defhelper also made a: " (pretty e2)
            debugM "giving me a: " (pretty $ Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy t) id e1)
            subst <- conv $ combineSubstitutions nullSpanNoFile sub1 sub2
            return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy t) id e1, delta2, subst, bindings1 ++ bindings2, True)
          else none
        _ -> none
    _ -> none)
defHelper left (def@(x, t) : right) gamma add@(Additive mode) grade goalTy@(Forall _ binders constraints goalTy') =
 defHelper (def:left) right gamma add grade goalTy `try`
 (case t of
    (FunTy _ tyA tyB) -> do
      x2 <- freshIdentifier
      debugM "entered def helper t: " (pretty t ++ " \n goal: " <> pretty goalTy <> " \n gamma: " <> show gamma)
      let (gamma', omega') = bindToContext (x2, (Linear tyB, None)) gamma [] (isLAsync tyB)
      (e1, delta1, sub1, bindings1, sd1) <- synthesiseInner (left++right) False add gamma' omega' grade goalTy (False, False, False)
      case lookupAndCutout x2 delta1 of
        Just (delta1', (Linear _, _)) -> do
          gamma2 <-
            case mode of
              Default -> return gamma
              Alternative -> ctxtSubtract (gamma' ++ omega') delta1'

          debugM "defHelper gamma2: " (show gamma2)
          debugM "defHelper binding: " (pretty x2)

          debugM "defHelper e1: " (pretty e1)

          (e2, delta2, sub2, bindings2, sd2) <- synthesiseInner (left++right) False add gamma2 [] grade (Forall nullSpanNoFile binders constraints tyA) (False, False, False)
          if sd2 then do

            debugM "defHelper gamma2: " (show gamma2)
            debugM "defHelper binding: " (pretty x2)
            debugM "defHelper e1: " (pretty e1)
            debugM "defHelper e2: " (pretty e2 <> " for " <> pretty tyA)

            -- Add the results
            deltaOut' <- maybeToSynthesiser $ ctxtAdd delta1' delta2

            subst <- conv $ combineSubstitutions nullSpan sub1 sub2
            return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy tyA) x2 e1, deltaOut', subst, bindings1 ++ bindings2, True)
          else none
        _ -> none
    _ -> none)

  -- where

    -- Take a variable representing a recursive function definition and a possible argument
    -- struct fun arg = undefined

synthesiseInner :: (?globals :: Globals)
           => Ctxt Type
           -> Bool               -- Does this call immediately follow a dereliction?
           -> ResourceScheme AltOrDefault      -- whether the synthesis is in additive mode or not
           -> Ctxt (Assumption, Structure Id)    -- (unfocused) free variables
           -> Ctxt (Assumption, Structure Id)    -- focused variables
           -> Maybe Type
           -> TypeScheme           -- type from which to synthesise
           -> (Bool, Bool, Bool)
           -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure Id), Substitution, Bindings, Bool)
synthesiseInner defs inDereliction resourceScheme gamma omega grade goalTy@(Forall _ binders _ goalTy') (allowLAsync, allowRSync, allowDef) = do
  debugM "synthDebug" $ "Synth inner with gamma = " ++ show gamma ++ ", and omega = "
                      ++ show omega ++ ", for goal = " ++ pretty goalTy
                      ++ ", isRAsync goalTy = " ++ show (isRAsync goalTy')
                      ++ ", isAtomic goalTy = " ++ show (isAtomic goalTy')
                      ++ ", allowRSync = " ++ show allowRSync
                      ++ ", allowLASync = " ++ show allowLAsync
                      ++ ", allowDef = " ++ show allowDef
                      ++ ", defs = " ++ show defs
  currentTime    <- liftIO $ Clock.getTime Clock.Monotonic
  state <- Synthesiser $ lift $ lift $ lift get
  -- let elapsedTime = round $ fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec currentTime startTime)) / (10^(6 :: Integer)::Double)
  if elapsedTime (startTime state) currentTime > synthTimeoutMillis && synthTimeoutMillis > 0 then Synthesiser (fail "Timeout")  else
    case (isRAsync goalTy', omega, allowLAsync) of
      (True, _, _) ->
        -- Right Async : Decompose goalTy until synchronous
        varHelper [] (gamma ++ omega) resourceScheme grade goalTy
        `try`
        absHelper defs allowRSync gamma omega resourceScheme grade goalTy
      (False, x:xs, _) ->
        -- Left Async : Decompose assumptions until they are synchronous (eliminators on assumptions)
        let altSynthStructuring = fromMaybe False (globalsAltSynthStructuring ?globals) in
        if altSynthStructuring then -- && structurallyDecreasing state  then
              (
              varHelper [] (gamma ++ omega) resourceScheme grade goalTy
              `try`
              appHelper (allowRSync, allowDef) defs [] (gamma ++ omega) resourceScheme grade goalTy
              `try`
              boxHelper defs (gamma ++ omega) resourceScheme grade goalTy
              `try`
              constrIntroHelper (allowRSync, allowDef) defs (gamma ++ omega) resourceScheme grade goalTy
              `try`
              defHelper [] defs (gamma ++ omega) resourceScheme grade goalTy 
              )
              `try`
              unboxHelper defs [] omega gamma resourceScheme grade goalTy
              `try`
              constrElimHelper (allowRSync, allowDef) defs [] omega gamma resourceScheme grade goalTy
        else 
          varHelper [] (gamma ++ omega) resourceScheme grade goalTy
          `try`
          unboxHelper defs [] omega gamma resourceScheme grade goalTy
          `try`
          constrElimHelper (allowRSync, allowDef) defs [] omega gamma resourceScheme grade goalTy


      (False, _, _) ->
              varHelper [] (gamma ++ omega) resourceScheme grade goalTy
              `try`
              appHelper (allowRSync, allowDef) defs [] (gamma ++ omega) resourceScheme grade goalTy
              `try`
              boxHelper defs (gamma ++ omega) resourceScheme grade goalTy
              `try`
              constrIntroHelper (allowRSync, allowDef) defs (gamma ++ omega) resourceScheme grade goalTy
              `try`
              defHelper [] defs (gamma ++ omega) resourceScheme grade goalTy 

       --       `try`
       --       if allowDef then defHelper [] defs startTime (gamma ++ omega) resourceScheme goalTy else none

synthesise :: (?globals :: Globals)
           => Ctxt Type
           -> ResourceScheme AltOrDefault      -- whether the synthesis is in additive mode or not
           -> Ctxt (Assumption, Structure Id)    -- (unfocused) free variables
           -> Ctxt (Assumption, Structure Id)    -- focused variables
           -> TypeScheme           -- type from which to synthesise
           -> Synthesiser (Expr () Type, Ctxt (Assumption, Structure Id), Substitution)
synthesise defs resourceScheme gamma omega goalTy = do
  let gradeOnRule = fromMaybe False (globalsGradeOnRule ?globals)
  let initialGrade = if gradeOnRule then Just (TyGrade Nothing 1)  else Nothing
  relevantConstructors <- do
      let snd3 (a, b, c) = b
          tripleToTup (a, b, c) = (a, b)
      st <- get
      let pats = map (second snd3) (typeConstructors st)
      mapM (\ (a, b) -> do
          dc <- conv $ mapM (lookupDataConstructor nullSpanNoFile) b
          let sd = zip (fromJust $ lookup a pats) (catMaybes dc)
          return (a, ctxtMap tripleToTup sd)) pats

  Synthesiser $ lift $ lift $ lift $ modify (\state ->
            state {
             constructors = relevantConstructors
                  })

  result@(expr, ctxt, subst, bindings, _) <- synthesiseInner defs False resourceScheme gamma omega initialGrade goalTy (True, True, False)
  case resourceScheme of
    Subtractive{} -> do
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
           => Ctxt Type -- Top level definitions to use in synthesis
           -> Id        -- Top level definition of the current expression being synthesised 
           -> ResourceScheme AltOrDefault       -- whether the synthesis is in additive mode or not
           -> Ctxt Assumption    -- (unfocused) free variables
           -> Ctxt Assumption    -- focused variables
           -> TypeScheme           -- type from which to synthesise
           -> CheckerState
           -> IO [(Expr () Type, Ctxt (Assumption, Structure Id), Substitution)]
synthesiseProgram defs topLevelDef resourceScheme gamma omega goalTy checkerState = do
  start <- liftIO $ Clock.getTime Clock.Monotonic
  -- %%
  let gamma' = map (\(v, a) -> (v, (a, None))) gamma
  let omega' = map (\(v, a) -> (v, (a, None))) omega
  let synRes = synthesise defs resourceScheme gamma' omega' goalTy
  let initialState = SynthesisData {smtCallsCount= 0, smtTime= 0, proverTime= 0, theoremSizeTotal= 0, pathsExplored= 0, startTime=start, constructors=[], topLevelDef=topLevelDef, structurallyDecreasing = False}
  (synthResults, aggregate) <- runStateT (runSynthesiser synRes checkerState) initialState
  let results = rights (map fst synthResults)
  -- Force eval of first result (if it exists) to avoid any laziness when benchmarking
  () <- when benchmarking $ unless (null results) (return $ seq (show $ head results) ())
  -- %%
  end    <- liftIO $ Clock.getTime Clock.Monotonic

  let timeoutMsg = if elapsedTime start end > synthTimeoutMillis && synthTimeoutMillis > 0 then  " - Timeout after: " <> (show synthTimeoutMillis  <> "ms") else ""

  debugM "results no: " (pretty $ map ( \(e, _, _) -> e) results)
  debugM "synthDebug" ("Result = " ++ (case synthResults of ((Right (expr, _, _), _):_) -> pretty expr; _ -> "NO SYNTHESIS"))
  case results of
      -- Nothing synthed, so create a blank hole instead
      []    -> do
        debugM "Synthesiser" $ "No programs synthesised for " <> pretty goalTy
        printInfo $ "No programs synthesised" <> timeoutMsg
      _ ->
        case last results of
          (t, _, _) -> do
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
            <> ", timeout = " <> (if null timeoutMsg then "False" else "True")
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

-- Calculate theorem sizes

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

--------------------------------
-- Testing code

--topLevel :: (?globals :: Globals) => TypeScheme -> ResourceScheme AltOrDefault -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
--topLevel ts@(Forall _ binders constraints ty) resourceScheme = do
--  conv $ State.modify (\st -> st { tyVarContext = map (\(n, c) -> (n, (c, ForallQ))) binders})
--  synthesise [] True resourceScheme [] [] ts

testGlobals :: Globals
testGlobals = mempty
  { globalsNoColors = Just True
  , globalsSuppressInfos = Just True
  , globalsTesting = Just True
  }

--testSyn :: Bool -> IO ()
--testSyn useReprint =
--  let ty =
----        FunTy Nothing (Box (CInterval (CNat 2) (CNat 3)) (TyVar $ mkId "b") ) (FunTy Nothing (SumTy (TyVar $ mkId "a") (TyVar $ mkId "c")) (SumTy (ProdTy (TyVar $ mkId "a") (Box (CInterval (CNat 2) (CNat 2)) (TyVar $ mkId "b") )) (ProdTy (TyVar $ mkId "c") (Box (CInterval (CNat 3) (CNat 3)) (TyVar $ mkId "b") ))))
----        FunTy Nothing (TyVar $ mkId "a") (SumTy (TyVar $ mkId "b") (TyVar $ mkId "a"))
--        FunTy Nothing (Box (CNat 3) (TyVar $ mkId "a")) (FunTy Nothing (Box (CNat 6) (TyVar $ mkId "b") ) (Box (CNat 3) (ProdTy (ProdTy (TyVar $ mkId "b") (TyVar $ mkId "b")) (TyVar $ mkId "a")) ))
----        FunTy Nothing (Box (CNat 2) (TyVar $ mkId "a")) (ProdTy (TyVar $ mkId "a") (TyVar $ mkId "a"))
----        FunTy Nothing (FunTy Nothing (TyVar $ mkId "a") (FunTy Nothing (TyVar $ mkId "b") (TyVar $ mkId "c"))) (FunTy Nothing (TyVar $ mkId "b") (FunTy Nothing (TyVar $ mkId "a") (TyVar $ mkId "c")))
----        FunTy Nothing (TyVar $ mkId "a") (TyVar $ mkId "a")
----        FunTy Nothing (Box (CNat 2) (TyVar $ mkId "a")) (ProdTy (TyVar $ mkId "a") (TyVar $ mkId "a"))
--        in
--    let ts = (Forall nullSpanNoFile [(mkId "a", KType), (mkId "b", KType), (mkId "c", KType)] [] ty) in
--    let ?globals = testGlobals in do
--     -- State.modify (\st -> st { tyVarContext = map (\(n, c) -> (n, (c, ForallQ))) [(mkId "a", KType)]})
--    let res = testOutput $ topLevel ts (Subtractive Default) in -- [(mkId "y", Linear (TyVar $ mkId "b")), (mkId "x", Linear (TyVar $ mkId "a"))] [] ty
--        if length res == 0
--        then  (putStrLn "No inhabitants found.")
--        else  (forM_ res (\(ast, _, sub) -> putStrLn $
--                           (if useReprint then pretty (reprintAsDef (mkId "f") ts ast) else pretty ast) ++ "\n" ++ (show sub) ))
--
--testOutput :: Synthesiser a -> [a]
--testOutput res =
--  rights $ map fst $ fst $ unsafePerformIO $ runStateT (runSynthesiser res initState) mempty

--testData :: Synthesiser a -> SynthesisData
--testData res =
--  snd $ unsafePerformIO $ runSynthesiser res initState
