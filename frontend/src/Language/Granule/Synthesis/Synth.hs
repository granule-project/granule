{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# options_ghc -fno-warn-incomplete-uni-patterns #-}
module Language.Granule.Synthesis.Synth where

--import Data.List
--import Control.Monad (forM_)
--import System.IO.Unsafe
import qualified Data.Map as M

import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
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
import Control.Monad.Except
--import Control.Monad.Trans.List
--import Control.Monad.Writer.Lazy
import Control.Monad.State.Strict

import qualified Control.Monad.State.Strict as State (get)
import qualified System.Clock as Clock

import Language.Granule.Utils


solve :: (?globals :: Globals)
  => Synthesiser Bool
solve = do
  cs <- conv $ State.get
  let pred = Conj $ predicateStack cs
  debugM "synthDebug" ("SMT on pred = " ++ pretty pred)
  tyVars <- conv $ justCoeffectTypes nullSpanNoFile (tyVarContext cs)
  -- Prove the predicate
  start  <- liftIO $ Clock.getTime Clock.Monotonic
  constructors <- conv $ allDataConstructorNames
  (smtTime', result) <- liftIO $ provePredicate pred tyVars constructors
  -- Force the result
  _ <- return $ result `seq` result
  end    <- liftIO $ Clock.getTime Clock.Monotonic
  let proverTime' = fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double)

  --state <- Synthesiser $ lift $ lift $ lift get
  -- traceM  $ show state
  -- Update benchmarking data
  Synthesiser $ lift $ lift $ lift $ modify (\state ->
            state {
             smtCallsCount = 1 + (smtCallsCount state),
             smtTime = smtTime' + (smtTime state),
             proverTime = proverTime' + (proverTime state),
             theoremSizeTotal = (toInteger $ length tyVars) + (sizeOfPred pred) + (theoremSizeTotal state)
                  })

  case result of
    QED -> do
      debugM "synthDebug" "SMT said: Yes."
      return True
    NotValid s -> do
      debugM "synthDebug" "SMT said: No."
      return False
    SolverProofError msgs -> do
      return False
    OtherSolverError reason -> do
      return False
    Timeout -> do
      return False
    _ -> do
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
ctxtSubtract gam ((x, Ghost g2):del) =
  case lookupAndCutout x gam of
    Just (gam', Discharged t2 g1) -> do
      g3 <- g1 `gradeSub` g2
      ctx <- ctxtSubtract gam' del
      return ((x, Ghost g3) : ctx)
    _ -> none

gradeSub :: (?globals::Globals) => Type -> Type -> Synthesiser Type
gradeSub g g' = do
  -- g - g' = c
  -- therefore
  -- g = c + g'
  (kind, _, _) <- conv $ synthKind nullSpan g
  var <- conv $ freshTyVarInContext (mkId $ "c") kind
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
      return $ ((x, Discharged t (TyInfix TyOpTimes g1 g2)): ctxt)
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
      var <- conv $ freshTyVarInContext (mkId $ "c") kind
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
  return $ (x, Discharged t (operator (TyGrade (Just kind) 0) g)) : ctxt'

-- TODO: handle new ghost variable
ctxtMerge operator [] ((x, Ghost g) : ctxt) = do
  -- Left context has no `x`, so assume it has been weakened (0 gade)
  (kind, _, _) <- conv $ synthKind nullSpan g
  ctxt' <- ctxtMerge operator [] ctxt
  debugM "ctxtMerge ghost" (pretty kind <> ", " <> pretty g)
  return $ (x, Ghost (operator (TyGrade (Just kind) 0) g)) : ctxt'

--  * Cannot meet/join an empty context to one with linear assumptions
ctxtMerge _ [] ((_, Linear t) : ctxt) = none

-- Inductive cases
ctxtMerge operator ((x, Discharged t1 g1) : ctxt1') ctxt2 = do
  case lookupAndCutout x ctxt2 of
    Just (ctxt2', Discharged t2 g2) ->
      if t1 == t2 -- Just in case but should always be true
        then do
          ctxt' <- ctxtMerge operator ctxt1' ctxt2'
          return $ (x, Discharged t1 (operator g1 g2)) : ctxt'
        else none

    Just (_, Ghost{}) -> none

    Just (_, Linear _) -> none -- mode mismatch

    Nothing -> do
      -- Right context has no `x`, so assume it has been weakened (0 gade)
      ctxt' <- ctxtMerge operator ctxt1' ctxt2
      (kind, _, _) <- conv $ synthKind nullSpan g1
      return $ (x, Discharged t1 (operator g1 (TyGrade (Just kind) 0))) : ctxt'

ctxtMerge operator ((x, Ghost g1) : ctxt1') ctxt2 = do
  case lookupAndCutout x ctxt2 of
    Just (ctxt2', Ghost g2) ->
      do ctxt' <- ctxtMerge operator ctxt1' ctxt2'
         return $ (x, Ghost (operator g1 g2)) : ctxt'

    Just (_, Discharged{}) -> none

    Just (_, Linear _) -> none -- mode mismatch

    Nothing -> do
      -- Right context has no `x`, so assume it has been weakened (0 gade)
      ctxt' <- ctxtMerge operator ctxt1' ctxt2
      (kind, _, _) <- conv $ synthKind nullSpan g1
      debugM "ctxtMerge ghost" (pretty kind <> ", " <> pretty g1)
      return $ (x, Ghost (operator g1 (TyGrade (Just kind) 0))) : ctxt'

ctxtMerge operator ((x, Linear t1) : ctxt1') ctxt2 = do
  case lookupAndCutout x ctxt2 of
    Just (ctxt2', Linear t2) ->
      if t1 == t2 -- Just in case but should always be true
        then do
          ctxt' <- ctxtMerge operator ctxt1' ctxt2'
          return $ (x, Linear t1) : ctxt1'
        else none

    Just (_, Discharged{}) -> none -- mode mismatch
    Just (_, Ghost{}) -> none -- mode mismatch

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
ctxtAdd ((x, Ghost g1):xs) ys =
  case lookupAndCutout x ys of
    Just (ys', Ghost g2) -> do
      ctxt <- ctxtAdd xs ys'
      return $ (x, Ghost (TyInfix TyOpPlus g1 g2)) : ctxt
    Nothing -> do
      ctxt <- ctxtAdd xs ys
      return $ (x, Ghost g1) : ctxt
    _ -> Nothing
ctxtAdd ((x, Linear t1):xs) ys =
  case lookup x ys of
    Just (Linear t2) -> Nothing
    Nothing -> do
      ctxt <- ctxtAdd xs ys
      return $ (x, Linear t1) : ctxt
    _ -> Nothing

isRAsync :: Type -> Bool
isRAsync (FunTy {}) = True
isRAsync _ = False

isLAsync :: Type -> Bool
isLAsync (ProdTy{}) = True
isLAsync (SumTy{}) = True
isLAsync (Box{}) = True
isLAsync (TyCon (internalName -> "()")) = True
isLAsync _ = False

isAtomic :: Type -> Bool
isAtomic (TyVar {}) = True
isAtomic _ = False

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
  var <- conv $ freshTyVarInContext (mkId $ "c") kind
  conv $ existential var kind
  -- conv $ addPredicate (Impl [] (Con (Neq nullSpanNoFile (CZero kind) grade kind))
  --                              (Con (ApproximatedBy nullSpanNoFile (CPlus (TyVar var) (COne kind)) grade kind)))
  conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar var) (TyGrade (Just kind) 0)) grade kind)
  res <- solve
  case res of
    True -> do
      return (True, replace gamma name (Discharged t (TyVar var)), t)
    False -> do
      return (False, [], t)
useVar (name, Ghost grade) gamma Subtractive{} = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  var <- conv $ freshTyVarInContext (mkId $ "c") kind
  conv $ existential var kind
  conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar var) (TyGrade (Just kind) 0)) grade kind)
  debugM "useVar ghost" (pretty kind <> ", " <> pretty grade)
  res <- solve
  case res of
    True -> do
      return (True, replace gamma name (Ghost (TyVar var)), ghostType)
    False -> do
      return (False, [], ghostType)

-- Additive
useVar (name, Linear t) _ Additive{} = return (True, [(name, Linear t)], t)
useVar (name, Discharged t grade) _ Additive{} = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  return (True, [(name, (Discharged t (TyGrade (Just kind) 1)))], t)
useVar (name, Ghost grade) _ Additive{} = do
  (kind, _, _) <- conv $ synthKind nullSpan grade
  return (True, [(name, (Ghost (TyGrade (Just kind) 1)))], ghostType)


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
 (varHelper (var:left) right resourceScheme goalTy) `try`
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
  => Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
absHelper gamma omega resourceScheme goalTy@(Forall _ binders constraints (FunTy name t1 t2)) = do
    -- Fresh var
    id <- useBinderNameOrFreshen name

    -- Build recursive context depending on focus mode
    let (gamma', omega') =
          if isLAsync t1 then
            (gamma, ((id, Linear t1):omega))
          else
            (((id, Linear t1):gamma, omega))

    -- Synthesis body
    debugM "synthDebug" $ "Lambda-binding " ++ pretty [(id, Linear t1)]
    (e, delta, subst, bindings) <- synthesiseInner False resourceScheme gamma' omega' (Forall nullSpanNoFile binders constraints t2)

    -- Check resource use at the end
    case (resourceScheme, lookupAndCutout id delta) of
      (Additive{}, Just (delta', Linear _)) -> do
      -- `id` was used
        return (makeAbs id e goalTy, delta', subst, bindings)
      (Subtractive{}, Nothing) -> do
      -- `id` was used
        return (makeAbs id e goalTy, delta, subst, bindings)
      _ -> do
      -- `id` was not used!
        none
absHelper _ _ _ _ = none


appHelper :: (?globals :: Globals)
  => Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
appHelper left [] _ _ = none

{-
Subtractive

x2 ∉ Δ1
Γ, x2 : B ⊢ C ⇒ t1 ; Δ1
Δ1 ⊢ A ⇒ t2 ; Δ2
------------------------ :: app
Γ, x1 : A → B ⊢ C ⇒ [(x1 t2) / x2] t1 ; Δ2

-}
appHelper left (var@(x, a) : right) (sub@Subtractive{}) goalTy@(Forall _ binders constraints _ ) =
  (appHelper (var : left) right sub goalTy) `try`
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
          (e1, delta1, sub1, bindings1) <- synthesiseInner False sub gamma' omega'' goalTy
          case lookup id delta1 of
            Nothing -> do
              -- Check that `id` was used by `e1` (and thus is not in `delta1`)
              debugM "synthDebug" ("Inside app, try to synth the argument at type " ++ pretty t1)
              (e2, delta2, sub2, bindings2) <- synthesiseInner False sub delta1 [] (Forall nullSpanNoFile binders constraints t1)
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
appHelper left (var@(x, a) : right) (add@(Additive mode)) goalTy@(Forall _ binders constraints _ ) =
  (appHelper (var : left) right add goalTy) `try`
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
          (e1, delta1, sub1, bindings1) <- synthesiseInner False add gamma' omega' goalTy
          -- Make sure that `x2` appears in the result
          case lookupAndCutout x2 delta1 of
            Just (delta1',  Linear _) -> do
              -- Pruning subtraction

              gamma2 <-
                case mode of
                  Default     -> return (gamma' ++ omega')
                  Alternative -> ctxtSubtract (gamma' ++ omega') delta1'

              -- Synthesise the argument
              (e2, delta2, sub2, bindings2) <- synthesiseInner False add gamma2 [] (Forall nullSpanNoFile binders constraints tyA)

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
  => Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
boxHelper gamma resourceScheme goalTy =
  case goalTy of
    (Forall _ binders constraints (Box g t)) -> do
      case resourceScheme of
        Additive{} ->
          do
            (e, delta, subst, bindings) <- synthesiseInner False resourceScheme gamma [] (Forall nullSpanNoFile binders constraints t)
            delta' <- ctxtMultByCoeffect g delta
            return (makeBox goalTy e, delta', subst, bindings)
        Subtractive Default ->
          do
            (e, delta, subst, bindings) <- synthesiseInner False resourceScheme gamma [] (Forall nullSpanNoFile binders constraints t)
            used <- ctxtSubtract gamma delta
            -- Compute what was used to synth e
            delta' <- ctxtMultByCoeffect g used
            delta'' <- ctxtSubtract gamma delta'
            return (makeBox goalTy e, delta'', subst, bindings)

        Subtractive Alternative -> do
          debugM "synthDebug" $ "div for " <> pretty goalTy
          gamma' <- ctxtDivByCoeffect g gamma
          debugM "synthDebug" $ "gamma = " <> pretty gamma
          debugM "synthDebug" $ "gamma' = " <> pretty gamma'
          (e, delta, subst, bindings) <- synthesiseInner False resourceScheme gamma' [] (Forall nullSpanNoFile binders constraints t)
          delta' <- ctxtMultByCoeffect g delta
          res <- solve
          case res of
            True -> do
              return (makeBox goalTy e, delta', subst, bindings)
            False -> none
    _ -> none


unboxHelper :: (?globals :: Globals)
  => Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
unboxHelper left [] _ _ _ = none

{-
Subtractive
0 <= s
Γ, x2 : [A] r ⊢ B ⇒ e ; Δ, x2 : [A] s
-------------------------------------------- :: unbox
Γ, x1 : [] r A ⊢ B ⇒ let [x2] = x1 in e; Δ

-}

unboxHelper left (var@(x1, a) : right) gamma (sub@Subtractive{}) goalTy =
  (unboxHelper (var : left) right gamma sub goalTy) `try` do
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
          (e, delta, subst, bindings) <- synthesiseInner False sub gamma' omega'' goalTy
          ---
          case lookupAndCutout x2 delta of
            Just (delta', (Discharged _ grade_s)) -> do
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
unboxHelper left (var@(x, a) : right) gamma (add@(Additive mode)) goalTy =
  (unboxHelper (var : left) right gamma add goalTy) `try`
   (case a of
     (Linear (Box grade t')) -> do
       let omega = (left ++ right)
       (canUse, omega', t) <- useVar var omega add
       if canUse
          then do
            x2 <- freshIdentifier
            -- omega1 <- ctxtSubtract omega omega'
            let (gamma', omega'') = bindToContext (x2, Discharged t' grade) gamma omega (isLAsync t')

            -- Synthesise the body of a `let` unboxing
            (e, delta, subst, bindings) <- synthesiseInner False add gamma' omega'' goalTy

            -- Add usage at the binder to the usage in the body
            delta' <- maybeToSynthesiser $ ctxtAdd omega' delta

            case lookupAndCutout x2 delta' of
              Just (delta'', (Discharged _ usage)) -> do
                (kind, _, _) <- conv $ synthKind nullSpan grade

                debugM "check" (pretty usage ++ " <=? " ++ pretty grade)
                conv $ addConstraint (ApproximatedBy nullSpanNoFile usage grade kind)
                res <- solve
                case res of
                  True -> do
                    return (makeUnbox x2 x goalTy t' (Box grade t') e,  delta'', subst, (x, (x2, Box grade t')):bindings)
                  False -> do
                    none
              _ -> do
                (kind, _, _) <- conv $ synthKind nullSpan grade
                conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade kind)
                res <- solve
                case res of
                  True ->
                    return (makeUnbox x2 x goalTy t' (Box grade t') e,  delta', subst, (x, (x2, Box grade t')):bindings)
                  False -> none
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
  => Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
pairIntroHelper gamma (sub@Subtractive{}) goalTy =
  case goalTy of
    (Forall _ binders constraints (ProdTy t1 t2)) -> do
      (e1, delta1, subst1, bindings1) <- synthesiseInner False sub gamma [] (Forall nullSpanNoFile binders constraints t1)
      (e2, delta2, subst2, bindings2) <- synthesiseInner False sub delta1 [] (Forall nullSpanNoFile binders constraints t2)
      subst <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
      return (makePair t1 t2 e1 e2, delta2, subst, bindings1 ++ bindings2)
    _ -> none
pairIntroHelper gamma (add@(Additive mode)) goalTy =
  case goalTy of
    (Forall _ binders constraints (ProdTy t1 t2)) -> do
      (e1, delta1, subst1, bindings1) <- synthesiseInner False add gamma [] (Forall nullSpanNoFile binders constraints t1)

      gamma' <- case mode of
                  Default     -> return gamma              -- no-prunes
                  Alternative -> ctxtSubtract gamma delta1 -- pruning

      (e2, delta2, subst2, bindings2) <- synthesiseInner False add gamma' [] (Forall nullSpanNoFile binders constraints t2)
      delta3 <- maybeToSynthesiser $ ctxtAdd delta1 delta2
      subst <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
      return (makePair t1 t2 e1 e2, delta3, subst, bindings1 ++ bindings2)
    _ -> none


pairElimHelper :: (?globals :: Globals)
  => Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
pairElimHelper left [] _ _ _ = none
{-
Subtractive

x1 ∉ Δ
x2 ∉ Δ
Γ, x1 : A, x2 : B ⊢ C ⇒ t2 ; Δ
------------------------------------------------ :: pair_elim
Γ, x3 : A ⊗ B ⊢ C ⇒ let x1, x2 = x3 in t2 ; Δ

-}
pairElimHelper left (var@(x, a):right) gamma (sub@Subtractive{}) goalTy =
  (pairElimHelper (var:left) right gamma sub goalTy) `try`
   (case a of
      (Linear (ProdTy t1 t2)) -> do
        debugM "synthDebug" $ "Trying to eliminate product type " ++ pretty a

        let omega = left ++ right
        (canUse, omega', t) <- useVar var omega sub
        if canUse
          then do
            lId <- freshIdentifier
            rId <- freshIdentifier
            let (gamma', omega'') = bindToContext (lId, Linear t1) gamma omega' (isLAsync t1)
            let (gamma'', omega''') = bindToContext (rId, Linear t2) gamma' omega'' (isLAsync t2)

            debugM "synthDebug" $ "Synthesiser inside product elim for goal " ++ pretty goalTy
            (e, delta, subst, bindings) <- synthesiseInner False sub gamma'' omega''' goalTy
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
pairElimHelper left (var@(x, a):right) gamma (add@(Additive mode)) goalTy =
  (pairElimHelper (var:left) right gamma add goalTy) `try`
    (case a of
      (Linear (ProdTy t1 t2)) -> do
        let omega = left ++ right
        (canUse, singleUse, _) <- useVar var omega add
        if canUse
          then do
            lId <- freshIdentifier
            rId <- freshIdentifier
--            omega1 <- ctxtSubtract omega singleUse
            let (gamma', omega')   = bindToContext (lId, Linear t1) gamma omega (isLAsync t1)
            let (gamma'', omega'') = bindToContext (rId, Linear t2) gamma' omega' (isLAsync t2)
            (e, delta, subst, bindings) <- synthesiseInner False add gamma'' omega'' goalTy
            delta' <- maybeToSynthesiser $ ctxtAdd singleUse delta
            case lookupAndCutout lId delta' of
              Just (delta', Linear _) ->
                case lookupAndCutout rId delta' of
                  Just (delta''', Linear _) -> return (makePairElim x lId rId goalTy t1 t2 e, delta''', subst, bindings)
                  _ -> none
              _ -> none
          else none
      _ -> none)


derelictionHelper :: (?globals :: Globals)
  => Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
derelictionHelper left (var@(x, a):right) gamma (add@(Additive mode)) goalTy =
  (derelictionHelper (var:left) right gamma add goalTy) `try`
  (case a of
     Discharged ty g -> do
       let omega = (var:left) ++ right
       (canUse, singleUse, _) <- useVar var omega add
       if canUse
         then do
           y <- freshIdentifier
           let (gamma', omega') = bindToContext (y, Linear ty) gamma omega (isLAsync ty)
           (e, delta, subst, bindings) <- synthesiseInner True add gamma' omega' goalTy
           case lookupAndCutout y delta of
             Just (delta', Linear _) -> do
               delta'' <- maybeToSynthesiser $ ctxtAdd singleUse delta'
               return (Language.Granule.Syntax.Expr.subst (makeVar x goalTy) y e, delta'', subst, bindings)
             _ -> none
         else none
     _ -> none)
derelictionHelper left (var@(x, a):right) gamma (sub@(Subtractive mode)) goalTy =
  (derelictionHelper (var:left) right gamma sub goalTy) `try`
  (case a of
     Discharged ty g -> do
       let omega = left ++ right
       (canUse, omega', _) <- useVar var omega sub
       if canUse
         then do
           y <- freshIdentifier
           let (gamma', omega'') = bindToContext (y, Linear ty) gamma omega' (isLAsync ty)
           (e, delta, subst, bindings) <- synthesiseInner True sub gamma' omega'' goalTy
           case lookup y delta of
             Nothing -> do
               return (Language.Granule.Syntax.Expr.subst (makeVar x goalTy) y e, delta, subst, bindings)
             _ -> none
         else none
     _ -> none)
derelictionHelper _ _ _ _ _ = none


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
  => Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
unitElimHelper left [] _ _ _ = none
{-
Subtractive

Γ ⊢ C ⇒ t ; Δ
---------------------------------- :: unit_elim
Γ, x : 1 ⊢ C ⇒ let () = x in t ; Δ

-}
unitElimHelper left (var@(x,a):right) gamma (sub@Subtractive{}) goalTy = do
  (unitElimHelper (var:left) right gamma sub goalTy) `try`
    case (getAssumptionType a) of
      (TyCon (internalName -> "()")) -> do
        (e, delta, subst, bindings) <- synthesiseInner False sub gamma (left ++ right) goalTy
        return (makeUnitElim x e goalTy, delta, subst, bindings)
      _ -> none
{-
Additive

Γ ⊢ C ⇒ t ; D
------------------------------------------ :: unit_elim
Γ, x : 1 ⊢ C ⇒ let () = x in t ; Δ, x : 1

-}
unitElimHelper left (var@(x,a):right) gamma (add@Additive{}) goalTy =
  (unitElimHelper (var:left) right gamma add goalTy) `try`
    case (getAssumptionType a) of
      (TyCon (internalName -> "()")) -> do
        (e, delta, subst, bindings) <- synthesiseInner False add gamma (left ++ right) goalTy
        return (makeUnitElim x e goalTy, (var:delta), subst, bindings)
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
  => Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
sumIntroHelper gamma resourceScheme goalTy =
  case goalTy of
    (Forall _ binders constraints (SumTy t1 t2)) -> do
      try
        (do
            (e1, delta1, subst1, bindings1) <- synthesiseInner False resourceScheme gamma [] (Forall nullSpanNoFile binders constraints t1)
            return (makeEitherLeft t1 t2 e1, delta1, subst1, bindings1)

        )
        (do
            (e2, delta2, subst2, bindings2) <- synthesiseInner False resourceScheme gamma [] (Forall nullSpanNoFile binders constraints t2)
            return (makeEitherRight t1 t2 e2, delta2, subst2, bindings2)

        )
    _ -> none


sumElimHelper :: (?globals :: Globals)
  => Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
sumElimHelper left [] _ _ _ = none
{-
Subtractive

x2 ∉ Δ1
x3 ∉ Δ2
Γ, x2 : A ⊢ C ⇒ t1 ; Δ1
Γ, x3 : B ⊢ C ⇒ t2 ; Δ2
-------------------------------------------------------------------- :: sum_elim
Γ, x1 : A ⊕ B ⊢ C ⇒ case x1 of inl x2 → t1 | inr x3 → t2 ; Δ1 ⊓ Δ2

-}
sumElimHelper left (var@(x, a):right) gamma (sub@Subtractive{}) goalTy =
  (sumElimHelper (var:left) right gamma sub goalTy) `try`
  let omega = left ++ right in do
  (canUse, omega', t) <- useVar var omega sub
  case (canUse, t) of
    (True, SumTy t1 t2) -> do
      l <- freshIdentifier
      r <- freshIdentifier
      let (gamma', omega'') = bindToContext (l, Linear t1) gamma omega' (isLAsync t1)
      let (gamma'', omega''') = bindToContext (r, Linear t2) gamma omega' (isLAsync t2)
      (e1, delta1, subst1, bindings1) <- synthesiseInner False sub gamma' omega'' goalTy
      (e2, delta2, subst2, bindings2) <- synthesiseInner False sub gamma'' omega''' goalTy
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
sumElimHelper left (var@(x, a):right) gamma (add@(Additive mode)) goalTy =
  (sumElimHelper (var:left) right gamma add goalTy) `try`
  let omega = left ++ right in do
  (canUse, omega', t) <- useVar var omega add
  case (canUse, a) of
    (True, Linear (SumTy t1 t2)) -> do
      l <- freshIdentifier
      r <- freshIdentifier
      --omega1 <- ctxtSubtract omega omega'
      let (gamma', omega'') = bindToContext (l, Linear t1) gamma omega (isLAsync t1)
      let (gamma'', omega''') = bindToContext (r, Linear t2) gamma omega (isLAsync t2)
      (e1, delta1, subst1, bindings1) <- synthesiseInner False add gamma' omega'' goalTy
      (e2, delta2, subst2, bindings2) <- synthesiseInner False add gamma'' omega''' goalTy
      subst <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
      case (lookupAndCutout l delta1, lookupAndCutout r delta2) of
          (Just (delta1', Linear _), Just (delta2', Linear _)) -> do
            delta3 <- ctxtMerge (TyInfix TyOpJoin) delta1' delta2'
            delta3' <- maybeToSynthesiser $ ctxtAdd omega' delta3
            return (makeCase t1 t2 x l r e1 e2, delta3', subst, bindings1 ++ bindings2)
          _ -> none
    _ -> none



synthesiseInner :: (?globals :: Globals)
           => Bool               -- Does this call immediately follow a dereliction?
           -> ResourceScheme AltOrDefault      -- whether the synthesis is in additive mode or not
           -> Ctxt Assumption    -- (unfocused) free variables
           -> Ctxt Assumption    -- focused variables
           -> TypeScheme           -- type from which to synthesise
           -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution, Bindings)
synthesiseInner inDereliction resourceScheme gamma omega goalTy@(Forall _ binders _ goalTy') = do
  debugM "synthDebug" $ "Synth inner with gamma = " ++ pretty gamma ++ ", and omega = "
                      ++ pretty omega ++ ", for goal = " ++ pretty goalTy
                      ++ ", isRAsync goalTy = " ++ show (isRAsync goalTy')
                      ++ ", isAtomic goalTy = " ++ show (isAtomic goalTy')

  case (isRAsync goalTy', omega) of
    (True, omega) ->
      -- Right Async : Decompose goalTy until synchronous
      absHelper gamma omega resourceScheme goalTy `try` none
    (False, omega@(x:xs)) ->
      -- Left Async : Decompose assumptions until they are synchronous (eliminators on assumptions)
      unboxHelper [] omega gamma resourceScheme goalTy
      `try`
      pairElimHelper [] omega gamma resourceScheme goalTy
      `try`
      sumElimHelper [] omega gamma resourceScheme goalTy
      `try`
      unitElimHelper [] omega gamma resourceScheme goalTy
      `try`
      if inDereliction then do
        none
      else
        derelictionHelper [] omega gamma resourceScheme goalTy
    (False, []) ->
      (if not (isAtomic goalTy') then
          -- Right Sync : Focus on goalTy when goalTy is not atomic
          sumIntroHelper gamma resourceScheme goalTy
          `try`
          pairIntroHelper gamma resourceScheme goalTy
          `try`
          boxHelper gamma resourceScheme goalTy
          `try`
          unitIntroHelper gamma resourceScheme goalTy
       else none)
       -- Or can always try to do left sync:
       `try` (do
            -- Transition to synchronous (focused) search
            -- Left Sync: App rule + Init rules
            varHelper [] gamma resourceScheme goalTy
            `try`
            appHelper [] gamma resourceScheme goalTy)

synthesise :: (?globals :: Globals)
           => ResourceScheme AltOrDefault      -- whether the synthesis is in additive mode or not
           -> Ctxt Assumption    -- (unfocused) free variables
           -> Ctxt Assumption    -- focused variables
           -> TypeScheme           -- type from which to synthesise
           -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
synthesise resourceScheme gamma omega goalTy = do
  result@(expr, ctxt, subst, bindings) <- synthesiseInner False resourceScheme gamma omega goalTy
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
                        solve
                      Ghost grade -> do
                        (kind, _, _) <-  conv $ synthKind nullSpan grade
                        conv $ addConstraint (ApproximatedBy nullSpanNoFile (TyGrade (Just kind) 0) grade kind)
                        solve
                       ) ctxt
      if and consumed
        then return (expr, ctxt, subst)
        else none

    -- All linear variables should have been used
    -- and all graded assumptions should have usages which approximate their original assumption
    Additive{} -> do
      consumed <- mapM (\(id, a) ->
                    case lookup id ctxt of
                      Just (Linear{}) -> return True;
                      Just (Discharged _ gradeUsed) ->
                        case a of
                          Discharged _ gradeSpec -> do
                            (kind, _, _) <- conv $ synthKind nullSpan gradeUsed
                            conv $ addConstraint (ApproximatedBy nullSpanNoFile gradeUsed gradeSpec kind)
                            solve
                          _ -> return False
                      -- TODO: handling of new ghost variables
                      Just (Ghost gradeUsed) ->
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
  let synRes = synthesise resourceScheme gamma omega goalTy
  (synthResults, aggregate) <- (runStateT (runSynthesiser synRes checkerState) mempty)
  let results = rights (map fst synthResults)
  -- Force eval of first result (if it exists) to avoid any laziness when benchmarking
  () <- when benchmarking $ unless (null results) (return $ seq (show $ head results) ())
  -- %%
  end    <- liftIO $ Clock.getTime Clock.Monotonic

  debugM "synthDebug" ("Result = " ++ (case synthResults of ((Right (expr, _, _), _):_) -> pretty $ expr; _ -> "NO SYNTHESIS"))
  -- <benchmarking-output>
  if benchmarking
    then do
      -- Output raw data (used for performance evaluation)
      if benchmarkingRawData then do
        putStrLn $ "Measurement "
              <> "{ smtCalls = " <> (show $ smtCallsCount aggregate)
              <> ", synthTime = " <> (show $ fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double))
              <> ", proverTime = " <> (show $ proverTime aggregate)
              <> ", solverTime = " <> (show $ Language.Granule.Synthesis.Monad.smtTime aggregate)
              <> ", meanTheoremSize = " <> (show $ if (smtCallsCount aggregate) == 0 then 0 else (fromInteger $ theoremSizeTotal aggregate) / (fromInteger $ smtCallsCount aggregate))
              <> ", success = " <> (if length results == 0 then "False" else "True")
              <> " } "
      else do
        -- Output benchmarking info
        putStrLn $ "-------------------------------------------------"
        putStrLn $ "Result = " ++ (case synthResults of ((Right (expr, _, _), _):_) -> pretty $ expr; _ -> "NO SYNTHESIS")
        putStrLn $ "-------- Synthesiser benchmarking data (" ++ show resourceScheme ++ ") -------"
        putStrLn $ "Total smtCalls     = " ++ (show $ smtCallsCount aggregate)
        putStrLn $ "Total smtTime    (ms) = "  ++ (show $ Language.Granule.Synthesis.Monad.smtTime aggregate)
        putStrLn $ "Total proverTime (ms) = "  ++ (show $ proverTime aggregate)
        putStrLn $ "Total synth time (ms) = "  ++ (show $ fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double))
        putStrLn $ "Mean theoremSize   = " ++ (show $ (if (smtCallsCount aggregate) == 0 then 0 else fromInteger $ theoremSizeTotal aggregate) / (fromInteger $ smtCallsCount aggregate))
    else return ()
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
sizeOfPred (Conj ps) = 1 + (sum $ map sizeOfPred ps)
sizeOfPred (Disj ps) = 1 + (sum $ map sizeOfPred ps)
sizeOfPred (Impl binders p1 p2) = 1 + (toInteger $ length binders) + (sizeOfPred p1) + (sizeOfPred p2)
sizeOfPred (Con c) = sizeOfConstraint c
sizeOfPred (NegPred p) = 1 + (sizeOfPred p)
sizeOfPred (Exists _ _ p) = 1 + (sizeOfPred p)

sizeOfConstraint :: Constraint -> Integer
sizeOfConstraint (Eq _ c1 c2 _) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfConstraint (Neq _ c1 c2 _) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfConstraint (ApproximatedBy _ c1 c2 _) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfConstraint (Lub _ c1 c2 c3 _) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2) + (sizeOfCoeffect c3)
sizeOfConstraint (Lt _ c1 c2) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfConstraint (Gt _ c1 c2) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfConstraint (LtEq _ c1 c2) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfConstraint (GtEq _ c1 c2) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)

sizeOfCoeffect :: Type -> Integer
sizeOfCoeffect (TyInfix _ c1 c2) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
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
