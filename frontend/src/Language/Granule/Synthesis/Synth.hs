{-# LANGUAGE ImplicitParams #-}


{-# options_ghc -fno-warn-incomplete-uni-patterns #-}
module Language.Granule.Synthesis.Synth where

--import Data.List
--import Control.Monad (forM_)
--import System.IO.Unsafe
import qualified Data.Map as M

import Data.List (intersect)

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
import Data.Maybe (fromJust, catMaybes)
import Language.Granule.Synthesis.Splitting (generateCases)
import Control.Arrow (second)


solve :: (?globals :: Globals)
  => Synthesiser Bool
solve = do
  cs <- conv State.get
  let pred = Conj $ predicateStack cs
  debugM "synthDebug" ("SMT on pred = " ++ pretty pred)
  tyVars <- conv $ justCoeffectTypes nullSpanNoFile (tyVarContext cs)
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

ctxtSubtract :: (?globals :: Globals) => Ctxt Assumption  -> Ctxt Assumption -> Synthesiser (Ctxt Assumption)
ctxtSubtract gam [] = return gam
ctxtSubtract gam ((x, Linear t):del) =
  case lookupAndCutout x gam of
    Just (gam', _) -> ctxtSubtract gam' del
    Nothing -> none

ctxtSubtract gam ((x, Discharged t g2):del) =
  case lookupAndCutout x gam of
    Just (gam', Discharged t2 g1) -> do
      g3 <- g1 `gradeSub` g2
      ctx <- ctxtSubtract gam' del
      return ((x, Discharged t g3):ctx)
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

ctxtMultByCoeffect :: Type -> Ctxt Assumption -> Synthesiser (Ctxt Assumption)
ctxtMultByCoeffect _ [] = return []
ctxtMultByCoeffect g1 ((x, Discharged t g2):xs) = do
      ctxt <- ctxtMultByCoeffect g1 xs
      return ((x, Discharged t (TyInfix TyOpTimes g1 g2)): ctxt)
ctxtMultByCoeffect _ _ = none

ctxtDivByCoeffect :: (?globals :: Globals) => Type -> Ctxt Assumption -> Synthesiser (Ctxt Assumption)
ctxtDivByCoeffect _ [] = return []
ctxtDivByCoeffect g1 ((x, Discharged t g2):xs) =
    do
      ctxt <- ctxtDivByCoeffect g1 xs
      var <- gradeDiv g1 g2
      return ((x, Discharged t var): ctxt)
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
          -> Ctxt Assumption
          -> Ctxt Assumption
          -> Synthesiser (Ctxt Assumption)

-- Base cases
--  * Empties
ctxtMerge _ [] [] = return []

--  * Can meet/join an empty context to one that has graded assumptions
ctxtMerge operator [] ((x, Discharged t g) : ctxt) = do
  -- Left context has no `x`, so assume it has been weakened (0 gade)
  (kind, _, _) <- conv $ synthKind nullSpan g
  ctxt' <- ctxtMerge operator [] ctxt
  return $ (x, Discharged t g) : ctxt'
--  return $ (x, Discharged t (operator (TyGrade (Just kind) 0) g)) : ctxt'

--  * Cannot meet/join an empty context to one with linear assumptions
ctxtMerge _ [] ((_, Linear t) : ctxt) = none

-- Inductive cases
ctxtMerge operator ((x, Discharged t1 g1) : ctxt1') ctxt2 =
  case lookupAndCutout x ctxt2 of
    Just (ctxt2', Discharged t2 g2) ->
      if t1 == t2 -- Just in case but should always be true
        then do
          ctxt' <- ctxtMerge operator ctxt1' ctxt2'
          return $ (x, Discharged t1 (operator g1 g2)) : ctxt'

        else none

    Just (_, Linear _) -> none -- mode mismatch

    Nothing -> do
      -- Right context has no `x`, so assume it has been weakened (0 gade)
      ctxt' <- ctxtMerge operator ctxt1' ctxt2
      (kind, _, _) <- conv $ synthKind nullSpan g1
      return $ (x, Discharged t1 g1) : ctxt'
      --return $ (x, Discharged t1 (operator g1 (TyGrade (Just kind) 0))) : ctxt'

ctxtMerge operator ((x, Linear t1) : ctxt1') ctxt2 =
  case lookupAndCutout x ctxt2 of
    Just (ctxt2', Linear t2) ->
      if t1 == t2 -- Just in case but should always be true
        then do
          ctxt' <- ctxtMerge operator ctxt1' ctxt2'
          return $ (x, Linear t1) : ctxt1'
        else none

    Just (_, Discharged{}) -> none -- mode mismatch

    Nothing -> none -- Cannot weaken a linear thing

ctxtAdd :: Ctxt Assumption -> Ctxt Assumption -> Maybe (Ctxt Assumption)
ctxtAdd [] y = Just y
ctxtAdd ((x, Discharged t1 g1):xs) ys =
  case lookupAndCutout x ys of
    Just (ys', Discharged t2 g2) -> do
      ctxt <- ctxtAdd xs ys'
      return $ (x, Discharged t1 (TyInfix TyOpPlus g1 g2)) : ctxt
    Nothing -> do
      ctxt <- ctxtAdd xs ys
      return $ (x, Discharged t1 g1) : ctxt
    _ -> Nothing
ctxtAdd ((x, Linear t1):xs) ys =
  case lookup x ys of
    Just (Linear t2) -> Nothing
    Nothing -> do
      ctxt <- ctxtAdd xs ys
      return $ (x, Linear t1) : ctxt
    _ -> Nothing

isRAsync :: Type -> Bool
isRAsync FunTy {} = True
isRAsync _ = False

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

data AltOrDefault = Default | Alternative
  deriving (Show, Eq)

data ResourceScheme a = Additive a | Subtractive a
  deriving (Show, Eq)


bindToContext :: (Id, Assumption) -> Ctxt Assumption -> Ctxt Assumption -> Bool -> (Ctxt Assumption, Ctxt Assumption)
bindToContext var gamma omega True = (gamma, omega ++ [var])
bindToContext var gamma omega False = (gamma ++ [var], omega)


-- Note that the way this is used, the (var, assumption) pair in the first
-- argument is not contained in the provided context (second argument)
useVar :: (?globals :: Globals) => (Id, Assumption) -> Ctxt Assumption -> ResourceScheme AltOrDefault -> Synthesiser (Bool, Ctxt Assumption, Type)

-- Subtractive
useVar (name, Linear t) gamma Subtractive{} = return (True, gamma, t)
useVar (name, Discharged t grade) gamma Subtractive{} = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  var <- conv $ freshTyVarInContext (mkId "c") kind
  conv $ existential var kind
  -- conv $ addPredicate (Impl [] (Con (Neq nullSpanNoFile (CZero kind) grade kind))
  --                              (Con (ApproximatedBy nullSpanNoFile (CPlus (TyVar var) (COne kind)) grade kind)))
  conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar var) (TyGrade (Just kind) 1)) grade kind)
  res <- solve
  if res then
    return (True, replace gamma name (Discharged t (TyVar var)), t) else
    return (False, [], t)

-- Additive
useVar (name, Linear t) _ Additive{} = return (True, [(name, Linear t)], t)
useVar (name, Discharged t grade) _ Additive{} = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  return (True, [(name, Discharged t (TyGrade (Just kind) 1))], t)


type Bindings = [(Id, (Id, Type))]

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
  => Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
varHelper left [] _ _ = none
varHelper left (var@(x, a) : right) resourceScheme goalTy@(Forall _ binders constraints goalTy') =
 varHelper (var:left) right resourceScheme goalTy `try`
   (do
      (success, specTy, subst) <- conv $ equalTypes nullSpanNoFile (getAssumptionType a) goalTy'
      if success then do
          (canUse, gamma, t) <- useVar var (left ++ right) resourceScheme
          boolToSynthesiser canUse (makeVar x goalTy, gamma, subst, [])
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
  => Clock.TimeSpec
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
absHelper startTime gamma omega resourceScheme goalTy@(Forall _ binders constraints (FunTy name t1 t2)) = do
    -- Fresh var
    id <- useBinderNameOrFreshen name

    -- Build recursive context depending on focus mode
    let (gamma', omega') =
          if isLAsync t1 then
            (gamma, (id, Linear t1):omega)
          else
            ((id, Linear t1):gamma, omega)

    -- Synthesis body
    debugM "synthDebug" $ "Lambda-binding " ++ pretty [(id, Linear t1)]
    (e, delta, subst, bindings) <- synthesiseInner startTime False resourceScheme gamma' omega' (Forall nullSpanNoFile binders constraints t2)

    -- Check resource use at the end
    case (resourceScheme, lookupAndCutout id delta) of
      (Additive{}, Just (delta', Linear _)) ->
        return (makeAbs id e goalTy, delta', subst, bindings)
      (Subtractive{}, Nothing) ->
        return (makeAbs id e goalTy, delta, subst, bindings)
      _ ->
        none
absHelper _ _ _ _ _ = none


appHelper :: (?globals :: Globals)
  => Clock.TimeSpec
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
appHelper _ left [] _ _ = none

{-
Subtractive

x2 ∉ Δ1
Γ, x2 : B ⊢ C ⇒ t1 ; Δ1
Δ1 ⊢ A ⇒ t2 ; Δ2
------------------------ :: app
Γ, x1 : A → B ⊢ C ⇒ [(x1 t2) / x2] t1 ; Δ2

-}
appHelper startTime left (var@(x, a) : right) sub@Subtractive{} goalTy@(Forall _ binders constraints _ ) =
  appHelper startTime (var : left) right sub goalTy `try`
  (case getAssumptionType a of
    (FunTy _ t1 t2) -> do
      debugM "synthDebug" ("Trying to use a function " ++ pretty var ++ " to get goal " ++ pretty goalTy)

      let omega = left ++ right
      (canUse, omega', t) <- useVar var omega sub
      if canUse
        then do
          id <- freshIdentifier
          let (gamma', omega'') = bindToContext (id, Linear t2) omega' [] (isLAsync t2)

          debugM "synthDebug" ("Inside app, try to synth the goal " ++ pretty goalTy ++ " under context of " ++ pretty [(id, Linear t2)])
          (e1, delta1, sub1, bindings1) <- synthesiseInner startTime False sub gamma' omega'' goalTy
          case lookup id delta1 of
            Nothing -> do
              -- Check that `id` was used by `e1` (and thus is not in `delta1`)
              debugM "synthDebug" ("Inside app, try to synth the argument at type " ++ pretty t1)
              (e2, delta2, sub2, bindings2) <- synthesiseInner startTime False sub delta1 [] (Forall nullSpanNoFile binders constraints t1)
              subst <- conv $ combineSubstitutions nullSpanNoFile sub1 sub2
              return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy t) id e1, delta2, subst, bindings1 ++ bindings2)
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
appHelper startTime left (var@(x, a) : right) add@(Additive mode) goalTy@(Forall _ binders constraints _ ) =
  appHelper startTime (var : left) right add goalTy `try`
  (case getAssumptionType a of
    (FunTy _ tyA tyB) -> do
      let omega = left ++ right
      (canUse, useContextOut, _) <- useVar var omega add
      if canUse
        then do
          x2 <- freshIdentifier
          -- Extend context (focussed) with x2 : B

          let (gamma', omega') = bindToContext (x2, Linear tyB) omega [] (isLAsync tyB)
          -- Synthesise new goal binding result `x2`
          (e1, delta1, sub1, bindings1) <- synthesiseInner startTime False add gamma' omega' goalTy
          -- Make sure that `x2` appears in the result
          case lookupAndCutout x2 delta1 of
            Just (delta1',  Linear _) -> do
              -- Pruning subtraction

              gamma2 <-
                case mode of
                  Default     -> return (gamma' ++ omega')
                  Alternative -> ctxtSubtract (gamma' ++ omega') delta1'

              -- Synthesise the argument
              (e2, delta2, sub2, bindings2) <- synthesiseInner startTime False add gamma2 [] (Forall nullSpanNoFile binders constraints tyA)

              -- Add the results
              deltaOut <- maybeToSynthesiser $ ctxtAdd useContextOut delta1'
              deltaOut' <- maybeToSynthesiser $ ctxtAdd deltaOut delta2

              subst <- conv $ combineSubstitutions nullSpan sub1 sub2
              return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy tyA) x2 e1, deltaOut', subst, bindings1 ++ bindings2)
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
  => Clock.TimeSpec
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
boxHelper startTime gamma resourceScheme goalTy =
  case goalTy of
    (Forall _ binders constraints (Box g t)) -> do
      case resourceScheme of
        Additive{} ->
          do
            (e, delta, subst, bindings) <- synthesiseInner startTime False resourceScheme gamma [] (Forall nullSpanNoFile binders constraints t)
            delta' <- ctxtMultByCoeffect g delta
            return (makeBox goalTy e, delta', subst, bindings)
        Subtractive Default ->
          do
            (e, delta, subst, bindings) <- synthesiseInner startTime False resourceScheme gamma [] (Forall nullSpanNoFile binders constraints t)
            used <- ctxtSubtract gamma delta
            -- Compute what was used to synth e
            delta' <- ctxtMultByCoeffect g used
            delta'' <- ctxtSubtract gamma delta'
            res <- solve
            boolToSynthesiser res (makeBox goalTy e, delta'', subst, bindings)

        Subtractive Alternative -> do
          gamma' <- ctxtDivByCoeffect g gamma
          (e, delta, subst, bindings) <- synthesiseInner startTime False resourceScheme gamma' [] (Forall nullSpanNoFile binders constraints t)
          delta' <- ctxtMultByCoeffect g delta
          res <- solve
          if res then
            return (makeBox goalTy e, delta', subst, bindings) else none
    _ -> none


unboxHelper :: (?globals :: Globals)
  => Clock.TimeSpec
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
unboxHelper _ left [] _ _ _ = none

{-
Subtractive
0 <= s
Γ, x2 : [A] r ⊢ B ⇒ e ; Δ, x2 : [A] s
-------------------------------------------- :: unbox
Γ, x1 : [] r A ⊢ B ⇒ let [x2] = x1 in e; Δ

-}

unboxHelper startTime left (var@(x1, a) : right) gamma sub@Subtractive{} goalTy =
  unboxHelper startTime (var : left) right gamma sub goalTy `try`
    (case getAssumptionType a of
      tyBoxA@(Box grade_r tyA) -> do
        debugM "synthDebug" $ "Trying to unbox " ++ pretty tyBoxA

        let omega = left ++ right
        (canUse, omega', _) <- useVar var omega sub
        if canUse then do
          --
          x2 <- freshIdentifier
          let (gamma', omega'') = bindToContext (x2, Discharged tyA grade_r) gamma omega' (isLAsync tyA)
          -- Synthesise inner
          debugM "synthDebug" $ "Inside unboxing try to synth for " ++ pretty goalTy ++ " under " ++ pretty [(x2, Discharged tyA grade_r)]
          (e, delta, subst, bindings) <- synthesiseInner startTime False sub gamma' omega'' goalTy
          ---
          case lookupAndCutout x2 delta of
            Just (delta', Discharged _ grade_s) -> do
              -- Check that: 0 <= s
              (kind, _, _) <- conv $ synthKind nullSpan grade_s
              conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade_s kind)
              res <- solve
              -- If we succeed, create the let binding
              boolToSynthesiser res (makeUnbox x2 x1 goalTy (Box grade_r tyA) tyA e, delta', subst, (x1, (x2, Box grade_r tyA)):bindings)

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
unboxHelper startTime left (var@(x, a) : right) gamma add@(Additive mode) goalTy =
  unboxHelper startTime (var : left) right gamma add goalTy `try`
   (case a of
     (Linear (Box grade t')) -> do
       let omega = left ++ right
       (canUse, omega', t) <- useVar var omega add
       if canUse
          then do
            x2 <- freshIdentifier
            -- omega1 <- ctxtSubtract omega omega'
            let (gamma', omega'') = bindToContext (x2, Discharged t' grade) gamma omega (isLAsync t')

            -- Synthesise the body of a `let` unboxing
            (e, delta, subst, bindings) <- synthesiseInner startTime False add gamma' omega'' goalTy

            -- Add usage at the binder to the usage in the body
            delta' <- maybeToSynthesiser $ ctxtAdd omega' delta

            case lookupAndCutout x2 delta' of
              Just (delta'', Discharged _ usage) -> do
                (kind, _, _) <- conv $ synthKind nullSpan grade

                debugM "check" (pretty usage ++ " <=? " ++ pretty grade)
                conv $ addConstraint (ApproximatedBy nullSpanNoFile usage grade kind)
                res <- solve
                if res then
                  return (makeUnbox x2 x goalTy t' (Box grade t') e,  delta'', subst, (x, (x2, Box grade t')):bindings) else none
              _ -> do
                (kind, _, _) <- conv $ synthKind nullSpan grade
                conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade kind)
                res <- solve
                if res then
                  return (makeUnbox x2 x goalTy t' (Box grade t') e,  delta', subst, (x, (x2, Box grade t')):bindings) else none
          else none
     _ -> none)

{-
Subtractive

Γ ⊢ A ⇒ t1 ; Δ1
Δ1 ⊢ B ⇒ t2 ; Δ2
------------------------ :: pair_intro
Γ ⊢ A * B ⇒ (t1, t2) ; Δ2

Additive

Γ ⊢ A ⇒ t1 ; Δ1
Γ ⊢ B ⇒ t2 ; Δ2
------------------------------ :: pair_intro
Γ ⊢ A ⊗ B ⇒ (t1, t2) ; Δ1 + Δ2

Additive Pruning

Γ |- A ⇒ t1 ; Δ1
Γ - Δ1 |- B ⇒ t2 ; Δ2
------------------------------- :: pair_intro
Γ |- A ⊗ B ⇒ (t1, t2) ; Δ1 + Δ2

-}
pairIntroHelper :: (?globals :: Globals)
  => Clock.TimeSpec
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
pairIntroHelper startTime gamma sub@Subtractive{} goalTy =
  case goalTy of
    (Forall _ binders constraints (ProdTy t1 t2)) -> do
      (e1, delta1, subst1, bindings1) <- synthesiseInner startTime False sub gamma [] (Forall nullSpanNoFile binders constraints t1)
      (e2, delta2, subst2, bindings2) <- synthesiseInner startTime False sub delta1 [] (Forall nullSpanNoFile binders constraints t2)
      subst <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
      return (makePair t1 t2 e1 e2, delta2, subst, bindings1 ++ bindings2)
    _ -> none
pairIntroHelper startTime gamma add@(Additive mode) goalTy =
  case goalTy of
    (Forall _ binders constraints (ProdTy t1 t2)) -> do
      (e1, delta1, subst1, bindings1) <- synthesiseInner startTime False add gamma [] (Forall nullSpanNoFile binders constraints t1)
      gamma' <- case mode of
                  Default     -> return gamma              -- no-prunes
                  Alternative -> ctxtSubtract gamma delta1 -- pruning

      (e2, delta2, subst2, bindings2) <- synthesiseInner startTime False add gamma' [] (Forall nullSpanNoFile binders constraints t2)

      delta3 <- maybeToSynthesiser $ ctxtAdd delta1 delta2
      subst <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
      return (makePair t1 t2 e1 e2, delta3, subst, bindings1 ++ bindings2)
    _ -> none


pairElimHelper :: (?globals :: Globals)
  => Clock.TimeSpec
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
pairElimHelper _ left [] _ _ _ = none
{-
Subtractive

x1 ∉ Δ
x2 ∉ Δ
Γ, x1 : A, x2 : B ⊢ C ⇒ t2 ; Δ
------------------------------------------------ :: pair_elim
Γ, x3 : A ⊗ B ⊢ C ⇒ let x1, x2 = x3 in t2 ; Δ

-}
pairElimHelper startTime left (var@(x, a):right) gamma sub@Subtractive{} goalTy =
  pairElimHelper startTime (var:left) right gamma sub goalTy `try`
   (case a of
      (Linear (ProdTy t1 t2)) -> do

        let omega = left ++ right
        (canUse, omega', t) <- useVar var omega sub
        if canUse
          then do
            lId <- freshIdentifier
            rId <- freshIdentifier
            let (gamma', omega'') = bindToContext (lId, Linear t1) gamma omega' (isLAsync t1)
            let (gamma'', omega''') = bindToContext (rId, Linear t2) gamma' omega'' (isLAsync t2)

            (e, delta, subst, bindings) <- synthesiseInner startTime False sub gamma'' omega''' goalTy
            case (lookup lId delta, lookup rId delta) of
              -- both `lId` and `rId` were used in `e`
              (Nothing, Nothing) -> return (makePairElim x lId rId goalTy t1 t2 e, delta, subst, bindings)
              _ -> none
          else none
      _ -> none)

{-
Additive

Γ, x1 : A, x2 : B ⊢ C ⇒ t2 ; Δ, x1 : A, x2 : B
------------------------------------------------------------ :: pair_elim
Γ, x3 : A ⊗ B ⊢ C ⇒ let x1, x2 = x3 in t2 ; Δ, x3 : A ⊗ B

-}
pairElimHelper startTime left (var@(x, a):right) gamma add@(Additive mode) goalTy =
  pairElimHelper startTime (var:left) right gamma add goalTy `try`
    (case a of
      (Linear (ProdTy t1 t2)) -> do
        let omega = left ++ right
        (canUse, singleUse, _) <- useVar var omega add
        if canUse
          then do
            debugM "in pair elim" ""
            lId <- freshIdentifier
            rId <- freshIdentifier
--            omega1 <- ctxtSubtract omega singleUse
            let (gamma', omega')   = bindToContext (lId, Linear t1) gamma omega (isLAsync t1)
            let (gamma'', omega'') = bindToContext (rId, Linear t2) gamma' omega' (isLAsync t2)
            (e, delta, subst, bindings) <- synthesiseInner startTime False add gamma'' omega'' goalTy
            delta' <- maybeToSynthesiser $ ctxtAdd singleUse delta
            case lookupAndCutout lId delta' of
              Just (delta', Linear _) ->
                case lookupAndCutout rId delta' of
                  Just (delta''', Linear _) -> return (makePairElim x lId rId goalTy t1 t2 e, delta''', subst, bindings)
                  _ -> none
              _ -> none
          else none
      _ -> none)



gradedPairElimHelper :: (?globals :: Globals)
  => Clock.TimeSpec
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
gradedPairElimHelper _ left [] _ _ _ = none
{-
Subtractive

x1 ∉ Δ
x2 ∉ Δ
Γ, x1 : A, x2 : B ⊢ C ⇒ t2 ; Δ
------------------------------------------------ :: pair_elim
Γ, x3 : A ⊗ B ⊢ C ⇒ let x1, x2 = x3 in t2 ; Δ

-}
gradedPairElimHelper startTime left (var@(x, a):right) gamma sub@Subtractive{} goalTySch@(Forall _ _ _ goalTy) =
  pairElimHelper startTime (var:left) right gamma sub goalTySch `try`
    (case a of
      (Discharged (ProdTy t1 t2) grade) -> do
        let omega = left ++ right
        (canUse, omega', _) <- useVar var omega sub
        if canUse then do
          let omega'' = deleteVar x omega'
          lId <- freshIdentifier
          rId <- freshIdentifier
          let (gamma', omega''')   = bindToContext (lId, Discharged t1 grade) gamma omega'' (isLAsync t1)
          let (gamma'', omega'''') = bindToContext (rId, Discharged t2 grade) gamma' omega''' (isLAsync t2)
          (e, delta, subst, bindings) <- synthesiseInner startTime False sub gamma'' omega'''' goalTySch
          let s = nullSpanNoFile
          let term = Case s goalTy False (Val s (ProdTy t1 t2) False (Promote (Box (ProdTy t1 t2) grade) (Val s (Box (ProdTy t1 t2) grade) False (Var (ProdTy t1 t2) x)) )) [(PBox s (Box (ProdTy t1 t2) grade) True (PConstr s (ProdTy t1 t2) False (mkId ",") [PVar s t1 False lId, PVar s t2 False rId]), e)]
          case (lookupAndCutout lId delta, lookupAndCutout rId delta) of
           (Just (lDelta, Discharged _ lUsage), Just (rDelta, Discharged _ rUsage)) -> do
             (kind, _, _) <- conv $ synthKind nullSpan grade
             conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) lUsage kind)
             conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) rUsage kind)
             res <- solve
             if res then do
               delta' <- ctxtMerge (TyInfix TyOpMeet) [(x, Discharged (ProdTy t1 t2) lUsage)] (lDelta `intersect` rDelta)
               delta'' <- ctxtMerge (TyInfix TyOpMeet) [(x, Discharged (ProdTy t1 t2) rUsage)] delta'
               return (term, delta'', subst, bindings)
             else none
           (_, _) -> none
        else none
      _ -> none)
{-
Additive

Γ, x1 : [A] r , x2 : [B] r ⊢ C ⇒ t2 ; Δ, x1 : [A] r, x2 : [B] r
------------------------------------------------------------ :: pair_elim
Γ, x3 : [A ⊗ B] r ⊢ C ⇒ case [x3] of [(x1, x2)] -> t ; Δ + x3 : [A ⊗ B] 1

-}
gradedPairElimHelper startTime left (var@(x, a):right) gamma add@(Additive mode) goalTySch@(Forall _ _ _ goalTy) =
  pairElimHelper startTime (var:left) right gamma add goalTySch `try`
    (case a of
      (Discharged (ProdTy t1 t2) grade) -> do
        let omega = left ++ right
        (canUse, singleUse, _) <- useVar var omega add
        if canUse then do
          lId <- freshIdentifier
          rId <- freshIdentifier
          let (gamma', omega')   = bindToContext (lId, Discharged t1 grade) gamma omega (isLAsync t1)
          let (gamma'', omega'') = bindToContext (rId, Discharged t2 grade) gamma' omega' (isLAsync t2)
          (e, delta, subst, bindings) <- synthesiseInner startTime False add gamma'' omega'' goalTySch
          let s = nullSpanNoFile
          let term = Case s goalTy False (Val s (ProdTy t1 t2) False (Promote (Box (ProdTy t1 t2) grade) (Val s (Box (ProdTy t1 t2) grade) False (Var (ProdTy t1 t2) x)) )) [(PBox s (Box (ProdTy t1 t2) grade) True (PConstr s (ProdTy t1 t2) False (mkId ",") [PVar s t1 False lId, PVar s t2 False rId]), e)]
          case (lookupAndCutout lId delta, lookupAndCutout rId delta) of
           (Just (lDelta, Discharged _ lUsage), Just (rDelta, Discharged _ rUsage)) -> do
             (kind, _, _) <- conv $ synthKind nullSpan grade
             conv $ addConstraint (ApproximatedBy nullSpanNoFile lUsage grade kind)
             conv $ addConstraint (ApproximatedBy nullSpanNoFile rUsage grade kind)
             res <- solve
             if res then do
               delta' <- ctxtMerge (TyInfix TyOpJoin) [(x, Discharged (ProdTy t1 t2) lUsage)] (lDelta `intersect` rDelta)
               delta'' <- ctxtMerge (TyInfix TyOpJoin) [(x, Discharged (ProdTy t1 t2) rUsage)] delta'
               return (term, delta'', subst, bindings)
             else none
           (Just (lDelta, Discharged _ lUsage), _) -> do
             (kind, _, _) <- conv $ synthKind nullSpan grade
             conv $ addConstraint (ApproximatedBy nullSpanNoFile lUsage grade kind)
             conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade kind)
             res <- solve
             if res then do
               delta' <- ctxtMerge (TyInfix TyOpJoin) [(x, Discharged (ProdTy t1 t2) lUsage)] delta
               return (term, delta', subst, bindings)
             else none
           (_, Just (rDelta, Discharged _ rUsage)) -> do
             (kind, _, _) <- conv $ synthKind nullSpan grade
             conv $ addConstraint (ApproximatedBy nullSpanNoFile rUsage grade kind)
             conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade kind)
             res <- solve
             if res then do
               delta' <- ctxtMerge (TyInfix TyOpJoin) [(x, Discharged (ProdTy t1 t2) rUsage)] delta
               return (term, delta', subst, bindings)
             else none
           (_, _) -> do
             (kind, _, _) <- conv $ synthKind nullSpan grade
             conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade kind)
             res <- solve
             if res then
               return (term, delta, subst, bindings)
             else none
        else none
      _ -> none)



derelictionHelper :: (?globals :: Globals)
  => Clock.TimeSpec
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
{-
Subtractive

Γ ; x : [A] s, y : A ⊢ B ⇒ t ; Δ, x : [A] s'
y ∉ D
∃s.r ⊒ s + 1
------------------------------------------------------------ :: dereliction
Γ ; x : [A] r ⊢ B ⇒ [x/y] t ; Δ, x : [A] s'

-}
derelictionHelper startTime left (var@(x, a):right) gamma sub@(Subtractive mode) goalTy =
  derelictionHelper startTime (var:left) right gamma sub goalTy `try`
  (case a of
     Discharged ty g -> do
       let omega = left ++ right
       (canUse, omega', _) <- useVar var omega sub
       if canUse
         then do
           y <- freshIdentifier
           let (gamma', omega'') = bindToContext (y, Linear ty) gamma omega' (isLAsync ty)
           debugM "Inside dereliction helper" ""
           (e, delta, subst, bindings) <- synthesiseInner startTime True sub gamma' omega'' goalTy
           case lookup y delta of
             Nothing ->
               return (Language.Granule.Syntax.Expr.subst (makeVar x goalTy) y e, delta, subst, bindings)
             _ -> none
         else none
     _ -> none)
{-
Additive

Γ ; x : [A] s, y : A ⊢ B ⇒ t ; Δ, y : A
------------------------------------------------------------ :: dereliction
Γ ; x : [A] s ⊢ B ⇒ [x/y] t ; Δ + x : [A] 1

-}
derelictionHelper startTime left (var@(x, a):right) gamma add@(Additive mode) goalTy =
  derelictionHelper startTime (var:left) right gamma add goalTy `try`
  (case a of
     Discharged ty g -> do
       let omega = left ++ right
       (canUse, singleUse, _) <- useVar var omega add
       if canUse
         then do
           y <- freshIdentifier
           debugM "in dereliction helper with gamma: " $ show gamma ++ " and omega " ++ show omega
           let (gamma', omega') = bindToContext (y, Linear ty) gamma omega (isLAsync ty)
           (e, delta, subst, bindings) <- synthesiseInner startTime True add gamma' (var:omega') goalTy
           case lookupAndCutout y delta of
             Just (delta', Linear _) -> do
               delta'' <- maybeToSynthesiser $ ctxtAdd singleUse delta'
               return (Language.Granule.Syntax.Expr.subst (makeVar x goalTy) y e, delta'', subst, bindings)
             _ -> none
         else none
     _ -> none)
derelictionHelper _ _ _ _ _ _ = none


{-
Subtractive

--------------- :: unit_intro
Γ ⊢ 1 ⇒ () ; Γ


Additive

--------------- :: unit_intro
Γ ⊢ 1 ⇒ () ; ∅

-}
unitIntroHelper ::
     Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
unitIntroHelper gamma resourceScheme goalTy =
  case goalTy of
    (Forall _ binders constraints (TyCon (internalName -> "()"))) -> do
      case resourceScheme of
        Additive{} -> return (makeUnitIntro, [], [], [])
        Subtractive{} -> return (makeUnitIntro, gamma, [], [])
    _ -> none



unitElimHelper :: (?globals :: Globals)
  => Clock.TimeSpec
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
unitElimHelper _ left [] _ _ _ = none
{-
Subtractive

Γ ⊢ C ⇒ t ; Δ
---------------------------------- :: unit_elim
Γ, x : 1 ⊢ C ⇒ let () = x in t ; Δ

-}
unitElimHelper startTime left (var@(x,a):right) gamma sub@Subtractive{} goalTy =
  unitElimHelper startTime (var:left) right gamma sub goalTy `try`
  case getAssumptionType a of
    (TyCon (internalName -> "()")) -> do
      (e, delta, subst, bindings) <- synthesiseInner startTime False sub gamma (left ++ right) goalTy
      return (makeUnitElim x e goalTy, delta, subst, bindings)
    _ -> none
{-
Additive

Γ ⊢ C ⇒ t ; D
------------------------------------------ :: unit_elim
Γ, x : 1 ⊢ C ⇒ let () = x in t ; Δ, x : 1

-}
unitElimHelper startTime left (var@(x,a):right) gamma add@Additive{} goalTy =
  unitElimHelper startTime (var:left) right gamma add goalTy `try`
    case getAssumptionType a of
      (TyCon (internalName -> "()")) -> do
        (e, delta, subst, bindings) <- synthesiseInner startTime False add gamma (left ++ right) goalTy
        return (makeUnitElim x e goalTy, var:delta, subst, bindings)
      _ -> none


{-
Subtractive

Γ ⊢ A ⇒ t ; D
------------------------ :: sum_intro_left
Γ ⊢ A ⊕ B ⇒ inl t ; Δ


Γ ⊢ B ⇒ t ; D
------------------------ :: sum_intro_right
Γ ⊢ A ⊕ B ⇒ inr t ; Δ


Additive

Γ ⊢ A ⇒ t ; Δ
------------------------ :: sum_intro_left
Γ ⊢ A ⊕ B ⇒ inl t ; Δ


Γ ⊢ B ⇒ t ; Δ
------------------------ :: sum_intro_right
Γ ⊢ A ⊕ B ⇒ inr t ; Δ

-}
sumIntroHelper :: (?globals :: Globals)
  => Clock.TimeSpec
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
sumIntroHelper startTime gamma resourceScheme goalTy =
  case goalTy of
    (Forall _ binders constraints (SumTy t1 t2)) ->
      try
      (do
          (e1, delta1, subst1, bindings1) <- synthesiseInner startTime False resourceScheme gamma [] (Forall nullSpanNoFile binders constraints t1)
          return (makeEitherLeft t1 t2 e1, delta1, subst1, bindings1)

      )
      (do
          (e2, delta2, subst2, bindings2) <- synthesiseInner startTime False resourceScheme gamma [] (Forall nullSpanNoFile binders constraints t2)
          return (makeEitherRight t1 t2 e2, delta2, subst2, bindings2)

      )
    _ -> none


sumElimHelper :: (?globals :: Globals)
  => Clock.TimeSpec
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
sumElimHelper _ left [] _ _ _ = none
{-
Subtractive

x2 ∉ Δ1
x3 ∉ Δ2
Γ, x2 : A ⊢ C ⇒ t1 ; Δ1
Γ, x3 : B ⊢ C ⇒ t2 ; Δ2
-------------------------------------------------------------------- :: sum_elim
Γ, x1 : A ⊕ B ⊢ C ⇒ case x1 of inl x2 → t1 | inr x3 → t2 ; Δ1 ⊓ Δ2

-}
sumElimHelper startTime left (var@(x, a):right) gamma sub@Subtractive{} goalTy =
  sumElimHelper startTime (var:left) right gamma sub goalTy `try`
  let omega = left ++ right in do
  (canUse, omega', t) <- useVar var omega sub
  case (canUse, t) of
    (True, SumTy t1 t2) -> do
      l <- freshIdentifier
      r <- freshIdentifier
      let (gamma', omega'') = bindToContext (l, Linear t1) gamma omega' (isLAsync t1)
      let (gamma'', omega''') = bindToContext (r, Linear t2) gamma omega' (isLAsync t2)
      (e1, delta1, subst1, bindings1) <- synthesiseInner startTime False sub gamma' omega'' goalTy
      (e2, delta2, subst2, bindings2) <- synthesiseInner startTime False sub gamma'' omega''' goalTy
      subst <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
      case (lookup l delta1, lookup r delta2) of
          (Nothing, Nothing) -> do
            -- Both `l` and `r` were used in `delta1` and `delta2` respectively
            delta3 <- ctxtMerge (TyInfix TyOpMeet) delta1 delta2
            return (makeCase t1 t2 x l r e1 e2, delta3, subst, bindings1 ++ bindings2)
          _ -> none
    _ -> none
{-
Additive

G, x2 : A ⊢ C ⇒ t1 ; Δ1, x2 : A
G, x3 : B ⊢ C ⇒ t2 ; Δ2, x3 : B
----------------------------------------------------------------------------------- :: sum_elim
G, x1 : A ⊕ B ⊢ C ⇒ case x1 of inl x2 → t1 | inr x3 → t2 ; (Δ1 ⊔ Δ2), x1 : A ⊕ B
-}
sumElimHelper startTime left (var@(x, a):right) gamma add@(Additive mode) goalTy =
  sumElimHelper startTime (var:left) right gamma add goalTy `try`
  let omega = left ++ right in do
  (canUse, omega', t) <- useVar var omega add
  case (canUse, a) of
    (True, Linear (SumTy t1 t2)) -> do
      l <- freshIdentifier
      r <- freshIdentifier
      --omega1 <- ctxtSubtract omega omega'
      let (gamma', omega'') = bindToContext (l, Linear t1) gamma omega (isLAsync t1)
      let (gamma'', omega''') = bindToContext (r, Linear t2) gamma omega (isLAsync t2)
      (e1, delta1, subst1, bindings1) <- synthesiseInner startTime False add gamma' omega'' goalTy
      (e2, delta2, subst2, bindings2) <- synthesiseInner startTime False add gamma'' omega''' goalTy
      subst <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
      case (lookupAndCutout l delta1, lookupAndCutout r delta2) of
          (Just (delta1', Linear _), Just (delta2', Linear _)) -> do
            delta3 <- ctxtMerge (TyInfix TyOpJoin) delta1' delta2'
            delta3' <- maybeToSynthesiser $ ctxtAdd omega' delta3
            return (makeCase t1 t2 x l r e1 e2, delta3', subst, bindings1 ++ bindings2)
          _ -> none
    _ -> none


constrIntroHelper :: (?globals :: Globals)
  => Clock.TimeSpec
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
constrIntroHelper startTime gamma mode goalTy@(Forall s binders constraints t) =
  case (isADT t, adtName t) of
    (True, Just name) -> do
      let snd3 (a, b, c) = b
      st <- get
      let pats = map (second snd3) (typeConstructors st)
      constructors <- conv $  mapM (\ (a, b) -> do
          dc <- mapM (lookupDataConstructor nullSpanNoFile) b
          let sd = zip (fromJust $ lookup a pats) (catMaybes dc)
          return (a, sd)) pats
      let adtConstructors = concatMap snd (filter (\x -> fst x == name) constructors)
      synthesiseConstructors gamma adtConstructors mode goalTy
    _ -> none
  where

    synthesiseConstructors gamma [] mode goalTy = none
    synthesiseConstructors gamma ((id, (Forall s binders' constraints' ty, subst, _)):cons) mode goalTy =
      case constrArgs ty of
        Just [] -> synthesiseConstructors gamma cons mode goalTy `try` do
          let delta = case mode of
                Additive{} -> []
                Subtractive{} -> gamma
          return (makeNullaryConstructor id, delta, subst, [])
        Just args -> synthesiseConstructors gamma cons mode goalTy `try` do
          (exprs, delta, subst', bindings) <- synthConstructorArgs args gamma mode subst
          return (makeConstr exprs id ty, delta, subst', bindings)
        Nothing ->
          none

    synthConstructorArgs [] _ _ _ = none
    synthConstructorArgs [t@(TyVar id)] gamma mode constrSubst = do
      conv $ modify (\st -> st { tyVarContext = (id, (ktype, BoundQ)) : tyVarContext st})
      (es, deltas, subst, bindings) <- synthesiseInner startTime False mode gamma [] (Forall s binders constraints t)
      subst' <- conv $ combineSubstitutions nullSpanNoFile constrSubst subst
      return ([(es, t)], deltas, subst', bindings)
    synthConstructorArgs (t@(TyVar id):ts) gamma mode constrSubst = do
      conv $ modify (\st -> st { tyVarContext = (id, (ktype, BoundQ)) : tyVarContext st})
      (es, deltas, subst, bindings) <- synthConstructorArgs ts gamma mode constrSubst
      subst' <- conv $ combineSubstitutions nullSpanNoFile constrSubst subst
      gamma2 <- case mode of
            Additive Default -> return gamma
            Additive Alternative -> ctxtSubtract gamma deltas -- Pruning
            Subtractive{} -> return deltas
      (e2, delta2, subst2, bindings2) <- synthesiseInner startTime False mode gamma2 [] (Forall s binders constraints t)
      subst'' <- conv $ combineSubstitutions nullSpanNoFile subst2 subst'
      delta3 <- case mode of
            Additive{} -> maybeToSynthesiser $ ctxtAdd deltas delta2
            Subtractive{} -> return delta2
      return ((e2, t):es, delta2, subst'', bindings ++ bindings2)
    synthConstructorArgs _ _ _ _ = none

    constrArgs (TyCon _) = Just []
    constrArgs (TyApp _ _) = Just []
    constrArgs (FunTy _ e1 e2) = do
      res <- constrArgs e2
      return $ e1 : res
    constrArgs _ = Nothing

    adtName (TyCon id) = Just id
    adtName (TyApp e1 e2) = adtName e1
    adtName _ = Nothing

constrElimHelper :: (?globals :: Globals)
  => Clock.TimeSpec
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
constrElimHelper startTime left [] _ _ _ = none
constrElimHelper startTime left (var@(x, a):right) gamma mode goalTySch@(Forall _ _ _ goalTy) =
  constrElimHelper startTime (var:left) right gamma mode goalTySch `try` do
    let omega = left ++ right
    (canUse, omega', _) <- useVar var omega mode
    case a of
      Linear t -> 
        if canUse && isADT t then do
          constrs <- constructors
          (_, cases) <- conv $ generateCases nullSpanNoFile constrs [var] [x] (Just $ FunTy Nothing t goalTy)
          case mode of
            Subtractive{} -> do
              (patterns, delta, subst, bindings') <- synthCases t mode gamma omega' cases goalTySch
              return (makeCase' t x patterns goalTy, delta, subst, bindings')
            Additive{} -> do
              (patterns, delta, subst, bindings') <- synthCases t mode gamma omega cases goalTySch
              delta2 <- maybeToSynthesiser $ ctxtAdd omega' delta
              return (makeCase' t x patterns goalTy, delta2, subst, bindings')
        else none
      Discharged t grade -> 
        if canUse && isADT t then do
          constrs <- constructors
          (_, cases) <- conv $ generateCases nullSpanNoFile constrs [(x, Linear (Box grade t))] [x] (Just $ FunTy Nothing (Box grade t) goalTy)
          case mode of
            Subtractive{} -> do
              let omega'' = deleteVar x omega'
              (patterns, delta, subst, bindings') <- synthCases t mode gamma omega'' cases goalTySch
              return (makeBoxCase t grade x patterns goalTy, delta, subst, bindings')
            Additive{} -> do
              (patterns, delta, subst, bindings') <- synthCases t mode gamma omega cases goalTySch
              return (makeBoxCase t grade x patterns goalTy, delta, subst, bindings')
        else none

  where

    constructors = do
      let snd3 (a, b, c) = b
      st <- get
      let pats = map (second snd3) (typeConstructors st)
      conv $  mapM (\ (a, b) -> do
        dc <- mapM (lookupDataConstructor nullSpanNoFile) b
        let sd = zip (fromJust $ lookup a pats) (catMaybes dc)
        return (a, sd)) pats

    synthCases adt mode g o [([p], assmps)] goalTy = do
      let (g', o', unboxed) = bindAssumptions assmps g o []
      (e, delta, subst, bindings) <- synthesiseInner startTime False mode g' o' goalTy
      del' <- checkAssumptions (x, getAssumptionType a) mode delta assmps unboxed
      case transformPattern bindings adt (g' ++ o') p unboxed of
        Just (pat, bindings') ->
          return ([(pat, e)], del', subst, bindings')
        Nothing -> none

    synthCases adt mode g o (([p], assmps):cons) goalTy = do
      (exprs, delta, subst, bindings) <- synthCases adt mode g o cons goalTy
      let (g', o', unboxed) = bindAssumptions assmps g o []
      (e, delta', subst', bindings') <- synthesiseInner startTime False mode g' o' goalTy
      del' <- checkAssumptions (x, getAssumptionType a) mode delta' assmps unboxed
      case transformPattern bindings' adt (g' ++ o') p unboxed of
        Just (pat, bindings'') ->
          let op = case mode of Additive{} -> TyInfix TyOpJoin ; _ -> TyInfix TyOpMeet
          in do
            returnDelta <- ctxtMerge op del' delta
            returnSubst <- conv $ combineSubstitutions nullSpanNoFile subst subst'
            return ((pat, e):exprs, returnDelta, returnSubst, bindings ++ bindings'')
        Nothing -> none
    synthCases adt mode g o _ goalTy = none




checkAssumptions :: (?globals::Globals) => (Id, Type) -> ResourceScheme a -> [(Id, Assumption)] -> [(Id, Assumption)] -> Ctxt Assumption -> Synthesiser [(Id, Assumption)]
checkAssumptions _ mode del [] _ = return del
checkAssumptions x sub@Subtractive{} del ((id, Linear t):assmps) unboxed =
  case lookup id del of
    Nothing -> checkAssumptions x sub del assmps unboxed
    _ -> none
checkAssumptions (x, t') sub@Subtractive{} del ((id, Discharged t g):assmps) unboxed = 
  case lookupAndCutout id del of
    Just (del', Discharged _ g') -> 
      case lookup id unboxed of 
        Just (Discharged _ g'') -> do
          del'' <- checkAssumptions (x, t') sub del' assmps unboxed
          (kind, _, _) <- conv $ synthKind nullSpan g'
          conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) g' kind)
          res <- solve
          if res then do
            ctxtMerge (TyInfix TyOpMeet) [(x, Discharged t' g)] del''
          else none
        _ -> do
          del'' <- checkAssumptions (x, t') sub del' assmps unboxed
          (kind, _, _) <- conv $ synthKind nullSpan g'
          conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) g' kind)
          res <- solve
          if res then  
            ctxtMerge (TyInfix TyOpMeet) [(x, Discharged t' g')] del''
          else none
    _ -> none
checkAssumptions x add@Additive{} del ((id, Linear t):assmps) unboxed =
  case lookupAndCutout id del of
    Just (del', _) ->
      checkAssumptions x add del' assmps unboxed
    _ -> none
checkAssumptions (x, t') sub@Additive{} del ((id, Discharged t g):assmps) unboxed = do
      case lookupAndCutout id del of
        Just (del', Discharged _ g') -> 
          case lookup id unboxed of 
            Just (Discharged _ g'') -> do
              del'' <- checkAssumptions (x, t') sub del' assmps unboxed
              (kind, _, _) <- conv $ synthKind nullSpan g'
              conv $ addConstraint (ApproximatedBy nullSpanNoFile g' g'' kind)
              res <- solve
              if res then do
                ctxtMerge (TyInfix TyOpJoin) [(x, Discharged t' g)] del''
              else none
            _ -> (do
              del'' <- checkAssumptions (x, t') sub del' assmps unboxed
              (kind, _, _) <- conv $ synthKind nullSpan g'
              conv $ addConstraint (ApproximatedBy nullSpanNoFile g' g kind)
              res <- solve
              if res then do
               ctxtMerge (TyInfix TyOpJoin) [(x, Discharged t' g')] del''
              else none)
        _ -> do
          (kind, _, _) <- conv $ synthKind nullSpan g
          conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) g kind)
          res <- solve
          if res then checkAssumptions (x, t') sub del assmps unboxed else none

bindAssumptions :: [(Id, Assumption)] -> Ctxt Assumption -> Ctxt Assumption -> Ctxt Assumption -> (Ctxt Assumption, Ctxt Assumption, Ctxt Assumption)
bindAssumptions [] g o unboxed = (g, o, unboxed)
bindAssumptions (assumption@(id, Linear t):assmps) g o unboxed =
  let (g', o') = bindToContext assumption g o (isLAsync t) in
  bindAssumptions assmps g' o'  unboxed
bindAssumptions (assumption@(id, Discharged (Box grade t) grade'):assmps) g o unboxed =
  let (g', o') = bindToContext (id, Discharged t (TyInfix TyOpTimes grade grade')) g o (isLAsync t) in
  bindAssumptions assmps g' o' ((id, Discharged t (TyInfix TyOpTimes grade grade')):unboxed)
bindAssumptions (assumption@(id, Discharged t _):assmps) g o unboxed =
  let (g', o') = bindToContext assumption g o (isLAsync t) in
  bindAssumptions assmps g' o' unboxed


-- Construct a typed pattern from an untyped one from the context
transformPattern :: Ctxt (Id, Type) -> Type -> [(Id, Assumption)] -> Pattern () -> Ctxt Assumption -> Maybe (Pattern Type, Ctxt (Id, Type))
transformPattern bindings adt ctxt (PConstr s () b id pats) unboxed = do
  (pats', bindings') <- transformPatterns bindings adt ctxt pats unboxed
  Just (PConstr s adt b id pats', bindings)
transformPattern bindings adt ctxt (PVar s () b name) unboxed =
  let (pat, name', bindings') = case lookup name unboxed of
        Just (Discharged ty _) -> (PBox s ty False, name, bindings)
        _ -> (id, name, bindings)
  in
  case lookup name ctxt of
     Just (Linear t) -> Just (pat $ PVar s t b name', bindings')
     Just (Discharged t c) -> Just (pat $ PVar s t b name', bindings')
     Nothing -> Nothing
transformPattern bindings adt ctxt (PBox s () b p) unboxed = do
  (pat', bindings') <- transformPattern bindings adt ctxt p unboxed
  Just (PBox s adt b pat', bindings')
transformPattern _ _ _ _ _ = Nothing

transformPatterns :: Ctxt (Id, Type) -> Type -> [(Id, Assumption)] -> [Pattern ()] -> Ctxt Assumption -> Maybe ([Pattern Type], Ctxt (Id, Type))
transformPatterns bindings adt ctxt [] unboxed = Just ([], bindings)
transformPatterns bindings adt ctxt (p:ps) unboxed = do
  (pat, bindings') <- transformPattern bindings adt ctxt p unboxed
  (res, bindingsFinal) <- transformPatterns bindings' adt ctxt ps unboxed
  return (pat:res, bindingsFinal)




linearVars :: Ctxt Assumption -> Ctxt Assumption
linearVars (var@(x, Linear a):xs) = var : linearVars xs
linearVars ((x, Discharged{}):xs) = linearVars xs
linearVars [] = []

synthesiseInner :: (?globals :: Globals)
           => Clock.TimeSpec
           -> Bool               -- Does this call immediately follow a dereliction?
           -> ResourceScheme AltOrDefault      -- whether the synthesis is in additive mode or not
           -> Ctxt Assumption    -- (unfocused) free variables
           -> Ctxt Assumption    -- focused variables
           -> TypeScheme           -- type from which to synthesise
           -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
synthesiseInner startTime inDereliction resourceScheme gamma omega goalTy@(Forall _ binders _ goalTy') = do
  debugM "synthDebug" $ "Synth inner with gamma = " ++ pretty gamma ++ ", and omega = "
                      ++ pretty omega ++ ", for goal = " ++ pretty goalTy
                      ++ ", isRAsync goalTy = " ++ show (isRAsync goalTy')
                      ++ ", isAtomic goalTy = " ++ show (isAtomic goalTy')
  currentTime    <- liftIO $ Clock.getTime Clock.Monotonic
  let elapsedTime = round $ fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec currentTime startTime)) / (10^(6 :: Integer)::Double)
  if elapsedTime > synthTimeoutMillis && synthTimeoutMillis > 0 then Synthesiser (lift $ fail "Timeout")  else
    case (isRAsync goalTy', omega) of
      (True, _) ->
        -- Right Async : Decompose goalTy until synchronous
        absHelper startTime gamma omega resourceScheme goalTy
      (False, x:xs) ->
        -- Left Async : Decompose assumptions until they are synchronous (eliminators on assumptions)
        unboxHelper startTime [] omega gamma resourceScheme goalTy
        `try`
        constrElimHelper startTime [] omega gamma resourceScheme goalTy
      (False, []) ->
        (if not (isAtomic goalTy') then
            -- Right Sync : Focus on goalTy when goalTy is not atomic
            sumIntroHelper startTime gamma resourceScheme goalTy
            `try`
            pairIntroHelper startTime gamma resourceScheme goalTy
            `try`
            boxHelper startTime gamma resourceScheme goalTy
            `try`
            unitIntroHelper gamma resourceScheme goalTy
        --    `try`
        --     constrIntroHelper startTime gamma resourceScheme goalTy
         else none)
        -- Or can always try to do left sync:
        `try` (
              varHelper [] gamma resourceScheme goalTy
              `try`
              appHelper startTime [] gamma resourceScheme goalTy)

synthesise :: (?globals :: Globals)
           => Clock.TimeSpec
           -> ResourceScheme AltOrDefault      -- whether the synthesis is in additive mode or not
           -> Ctxt Assumption    -- (unfocused) free variables
           -> Ctxt Assumption    -- focused variables
           -> TypeScheme           -- type from which to synthesise
           -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
synthesise startTime resourceScheme gamma omega goalTy = do
  result@(expr, ctxt, subst, bindings) <- synthesiseInner startTime False resourceScheme gamma omega goalTy
  case resourceScheme of
    Subtractive{} -> do
      -- All linear variables should be gone
      -- and all graded should approximate 0
      consumed <- mapM (\(id, a) ->
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
      consumed <- mapM (\(id, a) ->
                    case lookup id ctxt of
                      Just Linear{} -> return True;
                      Just (Discharged _ gradeUsed) ->
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
           => ResourceScheme AltOrDefault       -- whether the synthesis is in additive mode or not
           -> Ctxt Assumption    -- (unfocused) free variables
           -> Ctxt Assumption    -- focused variables
           -> TypeScheme           -- type from which to synthesise
           -> CheckerState
           -> IO [(Expr () Type, Ctxt Assumption, Substitution)]
synthesiseProgram resourceScheme gamma omega goalTy checkerState = do
  start <- liftIO $ Clock.getTime Clock.Monotonic
  -- %%
  let synRes = synthesise start resourceScheme gamma omega goalTy
  (synthResults, aggregate) <- runStateT (runSynthesiser synRes checkerState) mempty
  let results = rights (map fst synthResults)
  -- Force eval of first result (if it exists) to avoid any laziness when benchmarking
  () <- when benchmarking $ unless (null results) (return $ seq (show $ head results) ())
  -- %%
  end    <- liftIO $ Clock.getTime Clock.Monotonic

  debugM "synthDebug" ("Result = " ++ (case synthResults of ((Right (expr, _, _), _):_) -> pretty expr; _ -> "NO SYNTHESIS"))
  case results of
      -- Nothing synthed, so create a blank hole instead
      []    -> do
        debugM "Synthesiser" $ "No programs synthesised for " <> pretty goalTy
        printInfo "No programs synthesised"
      ((t, _, _):_) -> do
        debugM "Synthesiser" $ "Synthesised: " <> pretty t
        printSuccess "Synthesised"

  -- <benchmarking-output>
  when benchmarking $
      if benchmarkingRawData then do
        putStrLn $ "Measurement "
              <> "{ smtCalls = " <> show (smtCallsCount aggregate)
              <> ", synthTime = " <> show (fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double))
              <> ", proverTime = " <> show (proverTime aggregate)
              <> ", solverTime = " <> show (Language.Granule.Synthesis.Monad.smtTime aggregate)
              <> ", meanTheoremSize = " <> show (if smtCallsCount aggregate == 0 then 0 else fromInteger (theoremSizeTotal aggregate) / fromInteger (smtCallsCount aggregate))
              <> ", success = " <> (if null results then "False" else "True")
              <> " } "
      else do
        -- Output benchmarking info
        putStrLn $ "-------------------------------------------------"
        putStrLn $ "Result = " ++ (case synthResults of ((Right (expr, _, _), _):_) -> pretty $ expr; _ -> "NO SYNTHESIS")
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
