{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# options_ghc -fno-warn-incomplete-uni-patterns #-}
module Language.Granule.Synthesis.Synth where

--import Data.List
--import Control.Monad (forM_)
--import Debug.Trace
import System.IO.Unsafe
import qualified Data.Map as M

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.SecondParameter
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span

import Language.Granule.Context

-- import Language.Granule.Checker.Checker
import Language.Granule.Checker.Constraints
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.SubstitutionAndKinding
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Types
import Language.Granule.Checker.Variables
import Language.Granule.Synthesis.Builders
import Language.Granule.Synthesis.Refactor
import Language.Granule.Synthesis.Monad

import Data.Either (rights)
import Control.Monad.Except
import qualified Control.Monad.State.Strict as State (get, modify)
--import Control.Monad.Trans.List
--import Control.Monad.Writer.Lazy
import Control.Monad.State.Strict

import qualified System.Clock as Clock

import Language.Granule.Utils


solve :: (?globals :: Globals)
  => Synthesiser Bool
solve = do
  cs <- conv $ State.get
  let pred = pathToPredicate (predicateStack cs)
  debugM "synthDebug" ("SMT on pred = " ++ pretty pred)
  
  -- Prove the predicate
  start  <- liftIO $ Clock.getTime Clock.Monotonic
  (smtTime', result) <- liftIO $ provePredicate pred
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
             theoremSizeTotal = (sizeOfPred pred) + (theoremSizeTotal state)
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
    where
      gradeSub g g' = do
        -- g - g' = c
        -- therefore
        -- g = c + g'
        (kind, _) <- conv $ inferCoeffectType nullSpan g
        var <- conv $ freshTyVarInContext (mkId $ "c") (KPromote kind)
        conv $ existential var (KPromote kind)
        conv $ addConstraint (ApproximatedBy nullSpanNoFile (CPlus (CVar var) g') g kind)
        -- maximality
        varOther' <- conv $ freshIdentifierBase "cOther"
        let varOther = mkId varOther'
        conv $ predicate_addPredicate
                             (Forall varOther (KPromote kind)
                                (Impl 
                                  (Conj [Con $ ApproximatedBy nullSpanNoFile (CPlus (CVar varOther) g') g kind])
                                  (Conj [Con $ ApproximatedBy nullSpanNoFile (CVar varOther) (CVar var) kind])))
        return $ CVar var

ctxtMultByCoeffect :: Coeffect -> Ctxt Assumption -> Synthesiser (Ctxt Assumption)
ctxtMultByCoeffect _ [] = return []
ctxtMultByCoeffect g1 ((x, Discharged t g2):xs) = do
      ctxt <- ctxtMultByCoeffect g1 xs
      return $ ((x, Discharged t (CTimes g1 g2)): ctxt)
ctxtMultByCoeffect _ _ = none

ctxtDivByCoeffect :: (?globals :: Globals) => Coeffect -> Ctxt Assumption -> Synthesiser (Ctxt Assumption)
ctxtDivByCoeffect _ [] = return []
ctxtDivByCoeffect g1 ((x, Discharged t g2):xs) =
    do
      ctxt <- ctxtDivByCoeffect g1 xs
      var <- gradeDiv g1 g2
      return ((x, Discharged t var): ctxt)
  where
    gradeDiv g g' = do
      (kind, _) <- conv $ inferCoeffectType nullSpan g
      var <- conv $ freshTyVarInContext (mkId $ "c") (KPromote kind)
      conv $ existential var (KPromote kind)
      conv $ addConstraint (ApproximatedBy nullSpanNoFile (CTimes g (CVar var)) g' kind)
      return $ CVar var
ctxtDivByCoeffect _ _ = none

ctxtMerge :: (?globals :: Globals)
          => (Coeffect -> Coeffect -> Coeffect) -- lattice operator
          -> Ctxt Assumption
          -> Ctxt Assumption
          -> Synthesiser (Ctxt Assumption)

-- Base cases
--  * Empties
ctxtMerge _ [] [] = return []

--  * Can meet/join an empty context to one that has graded assumptions
ctxtMerge operator [] ((x, Discharged t g) : ctxt) = do
  -- Left context has no `x`, so assume it has been weakened (0 gade)
  (kind, _) <- conv $ inferCoeffectType nullSpan g
  ctxt' <- ctxtMerge operator [] ctxt
  return $ (x, Discharged t (operator (CZero kind) g)) : ctxt'

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

    Just (_, Linear _) -> none -- mode mismatch

    Nothing -> do
      -- Right context has no `x`, so assume it has been weakened (0 gade)
      ctxt' <- ctxtMerge operator ctxt1' ctxt2
      (kind, _) <- conv $ inferCoeffectType nullSpan g1
      return $ (x, Discharged t1 (operator g1 (CZero kind))) : ctxt'

ctxtMerge operator ((x, Linear t1) : ctxt1') ctxt2 = do
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
      return $ (x, Discharged t1 (CPlus g1 g2)) : ctxt
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

-- Reprint Expr as a top-level declaration
reprintAsDef :: Id -> TypeScheme -> Expr () Type -> Def () Type
reprintAsDef id goalTy expr =
  refactorDef $
    Def
      { defSpan = nullSpanNoFile,
        defId = id,
        defRefactored = False,
        defEquations =
          EquationList
            { equationsSpan = nullSpanNoFile,
              equationsId = id,
              equationsRefactored = False,
              equations =
              [ Equation
                { equationSpan = nullSpanNoFile,
                  equationId = id,
                  equationRefactored = True,
                  equationAnnotation = getSecondParameter expr,
                  equationPatterns = [],
                  equationBody = expr
                }
              ]
            }
          ,
      defTypeScheme = goalTy
      }

bindToContext :: (Id, Assumption) -> Ctxt Assumption -> Ctxt Assumption -> Bool -> (Ctxt Assumption, Ctxt Assumption)
bindToContext var gamma omega True = (gamma, omega ++ [var])
bindToContext var gamma omega False = (gamma ++ [var], omega)


-- Note that the way this is used, the (var, assumption) pair in the first
-- argument is not contained in the provided context (second argument)
useVar :: (?globals :: Globals) => (Id, Assumption) -> Ctxt Assumption -> ResourceScheme AltOrDefault -> Synthesiser (Bool, Ctxt Assumption, Type)

-- Subtractive
useVar (name, Linear t) gamma Subtractive{} = return (True, gamma, t)
useVar (name, Discharged t grade) gamma Subtractive{} = do
  (kind, _) <- conv $ inferCoeffectType nullSpan grade
  var <- conv $ freshTyVarInContext (mkId $ "c") (KPromote kind)
  conv $ existential var (KPromote kind)
  -- conv $ addPredicate (Impl [] (Con (Neq nullSpanNoFile (CZero kind) grade kind))
  --                              (Con (ApproximatedBy nullSpanNoFile (CPlus (CVar var) (COne kind)) grade kind)))
  conv $ addConstraint (ApproximatedBy nullSpanNoFile (CPlus (CVar var) (COne kind)) grade kind)
  res <- solve
  case res of
    True -> do
      return (True, replace gamma name (Discharged t (CVar var)), t)
    False -> do
      return (False, [], t)

-- Additive
useVar (name, Linear t) _ Additive{} = return (True, [(name, Linear t)], t)
useVar (name, Discharged t grade) _ Additive{} = do
  (kind, _) <- conv $ inferCoeffectType nullSpan grade
  return (True, [(name, (Discharged t (COne kind)))], t)

varHelper :: (?globals :: Globals)
  => Ctxt DataDecl
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
varHelper decls left [] _ _ = none
varHelper decls left (var@(x, a) : right) resourceScheme goalTy@(ForallTyS _ binders constraints goalTy') =
 (varHelper decls (var:left) right resourceScheme goalTy) `try`
   (do
--    liftIO $ putStrLn $ "synth eq on (" <> pretty var <> ") " <> pretty t <> " and " <> pretty goalTy'
      (success, specTy, subst) <- conv $ equalTypes nullSpanNoFile (getAssumptionType a) goalTy'
      if success then do
          (canUse, gamma, t) <- useVar var (left ++ right) resourceScheme
          boolToSynthesiser canUse (makeVar x goalTy, gamma, subst)
      else none)

absHelper :: (?globals :: Globals)
  => Ctxt DataDecl
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Bool
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
absHelper decls gamma omega allowLam resourceScheme goalTy@(ForallTyS _ binders constraints (FunTy name t1 t2)) = do
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
    (e, delta, subst) <- synthesiseInner decls True resourceScheme gamma' omega' (ForallTyS nullSpanNoFile binders constraints t2)

    -- Check resource use at the end
    case (resourceScheme, lookupAndCutout id delta) of
      (Additive{}, Just (delta', Linear _)) ->
        -- `id` was used
        return (makeAbs id e goalTy, delta', subst)
      (Subtractive{}, Nothing) ->
        -- `id` was used
        return (makeAbs id e goalTy, delta, subst)
      _ ->
        -- `id` was not used!
        none
absHelper _ _ _ _ _ _ = none


appHelper :: (?globals :: Globals)
  => Ctxt DataDecl
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
appHelper decls left [] _ _ = none

appHelper decls left (var@(x, a) : right) (sub@Subtractive{}) goalTy@(ForallTyS _ binders constraints _ ) =
  (appHelper decls (var : left) right sub goalTy) `try`
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
          (e1, delta1, sub1) <- synthesiseInner decls True sub gamma' omega'' goalTy
          case lookup id delta1 of
            Nothing -> do
              -- Check that `id` was used by `e1` (and thus is not in `delta1`)
              debugM "synthDebug" ("Inside app, try to synth the argument at type " ++ pretty t1)
              (e2, delta2, sub2) <- synthesiseInner decls True sub delta1 [] (ForallTyS nullSpanNoFile binders constraints t1)
              subst <- conv $ combineSubstitutions nullSpanNoFile sub1 sub2
              return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy t) id e1, delta2, subst)
            _ -> none
        else none
    _ -> none)

appHelper decls left (var@(x, a) : right) (add@(Additive mode)) goalTy@(ForallTyS _ binders constraints _ ) =
  (appHelper decls (var : left) right add goalTy) `try`
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
          (e1, delta1, sub1) <- synthesiseInner decls True add gamma' omega' goalTy
          -- Make sure that `x2` appears in the result
          case lookupAndCutout x2 delta1 of
            Just (delta1',  Linear _) -> do
              -- Pruning subtraction

              gamma2 <-
                case mode of
                  Default     -> return (gamma' ++ omega')
                  Alternative -> ctxtSubtract (gamma' ++ omega') delta1'

              -- Synthesise the argument
              (e2, delta2, sub2) <- synthesiseInner decls True add gamma2 [] (ForallTyS nullSpanNoFile binders constraints tyA)

              -- Add the results
              deltaOut <- maybeToSynthesiser $ ctxtAdd useContextOut delta1'
              deltaOut' <- maybeToSynthesiser $ ctxtAdd deltaOut delta2

              subst <- conv $ combineSubstitutions nullSpan sub1 sub2
              return (Language.Granule.Syntax.Expr.subst (makeApp x e2 goalTy tyA) x2 e1, deltaOut', subst)
            _ -> none
        else none
    _ -> none)

boxHelper :: (?globals :: Globals)
  => Ctxt DataDecl
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
boxHelper decls gamma resourceScheme goalTy =
  case goalTy of
    (ForallTyS _ binders constraints (Box g t)) -> do
      case resourceScheme of
        Additive{} ->
          do
            (e, delta, subst) <- synthesiseInner decls True resourceScheme gamma [] (ForallTyS nullSpanNoFile binders constraints t)
            delta' <- ctxtMultByCoeffect g delta
            return (makeBox goalTy e, delta', subst)
        Subtractive Default ->
          do
            (e, delta, subst) <- synthesiseInner decls True resourceScheme gamma [] (ForallTyS nullSpanNoFile binders constraints t)
            used <- ctxtSubtract gamma delta
            -- Compute what was used to synth e
            delta' <- ctxtMultByCoeffect g used
            delta'' <- ctxtSubtract gamma delta'
            return (makeBox goalTy e, delta'', subst)

        Subtractive Alternative -> do
          debugM "synthDebug" $ "div for " <> pretty goalTy
          gamma' <- ctxtDivByCoeffect g gamma
          debugM "synthDebug" $ "gamma = " <> pretty gamma
          debugM "synthDebug" $ "gamma' = " <> pretty gamma'
          (e, delta, subst) <- synthesiseInner decls True resourceScheme gamma' [] (ForallTyS nullSpanNoFile binders constraints t)
          delta' <- ctxtMultByCoeffect g delta
          res <- solve
          case res of
            True -> do
              return (makeBox goalTy e, delta', subst)
            False -> none
    _ -> none


unboxHelper :: (?globals :: Globals)
  => Ctxt DataDecl
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
unboxHelper decls left [] _ _ _ = none

{-

 G, x2 : [A]r |- B =>- e : Delta, x2 : [A]s   0 <= s
-------------------------------------------------------
  G, x1 : []r A |- B =>- let [x2] = x1 in e; Delta
-}

unboxHelper decls left (var@(x1, a) : right) gamma (sub@Subtractive{}) goalTy =
  (unboxHelper decls (var : left) right gamma sub goalTy) `try` do
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
          (e, delta, subst) <- synthesiseInner decls True sub gamma' omega'' goalTy
          ---
          case lookupAndCutout x2 delta of
            Just (delta', (Discharged _ grade_s)) -> do
              -- Check that: 0 <= s
              (kind, _) <- conv $ inferCoeffectType nullSpan grade_s
              conv $ addConstraint (ApproximatedBy nullSpanNoFile (CZero kind) grade_s kind)
              res <- solve
              -- If we succeed, create the let binding
              boolToSynthesiser res (makeUnbox x2 x1 goalTy tyBoxA tyA e, delta', subst)

            _ -> none
        else none
      _ -> none)

unboxHelper decls left (var@(x, a) : right) gamma (add@(Additive mode)) goalTy =
  (unboxHelper decls (var : left) right gamma add goalTy) `try`
   (case getAssumptionType a of
     (Box grade t') -> do
       let omega = var:(left ++ right)
       (canUse, omega', t) <- useVar var omega add
       if canUse
          then do
            x2 <- freshIdentifier
            omega1 <- ctxtSubtract omega omega'
            let (gamma', omega1') = bindToContext (x2, Discharged t' grade) gamma omega1 (isLAsync t')

            -- Synthesise the body of a `let` unboxing
            (e, delta, subst) <- synthesiseInner decls True add gamma' omega1' goalTy

            -- Add usage at the binder to the usage in the body
            delta' <- maybeToSynthesiser $ ctxtAdd omega' delta

            case lookupAndCutout x2 delta' of
              Just (delta'', (Discharged _ usage)) -> do
                (kind, _) <- conv $ inferCoeffectType nullSpan grade

                debugM "check" (pretty usage ++ " <=? " ++ pretty grade)
                conv $ addConstraint (ApproximatedBy nullSpanNoFile usage grade kind)
                res <- solve
                case res of
                  True -> do
                    return (makeUnbox x2 x goalTy t t' e,  delta'', subst)
                  False -> do
                    none
              _ -> do
                (kind, _) <- conv $ inferCoeffectType nullSpan grade
                conv $ addConstraint (ApproximatedBy nullSpanNoFile (CZero kind) grade kind)
                res <- solve
                case res of
                  True ->
                    return (makeUnbox x2 x goalTy t t' e,  delta', subst)
                  False -> none
          else none
     _ -> none)

pairElimHelper :: (?globals :: Globals)
  => Ctxt DataDecl
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
pairElimHelper decls left [] _ _ _ = none
pairElimHelper decls left (var@(x, a):right) gamma (sub@Subtractive{}) goalTy =
  (pairElimHelper decls (var:left) right gamma sub goalTy) `try`
   (case getAssumptionType a of
      (ProdTy t1 t2) -> do
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
            (e, delta, subst) <- synthesiseInner decls True sub gamma'' omega''' goalTy
            case (lookup lId delta, lookup rId delta) of
              -- both `lId` and `rId` were used in `e`
              (Nothing, Nothing) -> return (makePairElim x lId rId goalTy t1 t2 e, delta, subst)
              _ -> none
          else none
      _ -> none)

pairElimHelper decls left (var@(x, a):right) gamma (add@(Additive mode)) goalTy =
  (pairElimHelper decls (var:left) right gamma add goalTy) `try`
    (case getAssumptionType a of
      (ProdTy t1 t2) -> do
        let omega = (var:left) ++ right
        (canUse, omega', t) <- useVar var omega add
        if canUse
          then do
            lId <- freshIdentifier
            rId <- freshIdentifier
            omega1 <- ctxtSubtract omega omega'
            let (gamma', omega1')   = bindToContext (lId, Linear t1) gamma omega1 (isLAsync t1)
            let (gamma'', omega1'') = bindToContext (rId, Linear t2) gamma' omega1' (isLAsync t2)
            (e, delta, subst) <- synthesiseInner decls True add gamma'' omega1'' goalTy
            delta' <- maybeToSynthesiser $ ctxtAdd omega' delta
            case lookupAndCutout lId delta' of
              Just (delta', Linear _) ->
                case lookupAndCutout rId delta' of
                  Just (delta''', Linear _) -> return (makePairElim x lId rId goalTy t1 t2 e, delta''', subst)
                  _ -> none
              _ -> none
          else none
      _ -> none)

unitIntroHelper ::
     Ctxt DataDecl
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
unitIntroHelper decls gamma resourceScheme goalTy =
  case goalTy of
    (ForallTyS _ binders constraints (TyCon (internalName -> "()"))) -> do
      case resourceScheme of
        Additive{} -> return (makeUnitIntro, [], [])
        Subtractive{} -> return (makeUnitIntro, gamma, [])
    _ -> none

pairIntroHelper :: (?globals :: Globals)
  => Ctxt DataDecl
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
pairIntroHelper decls gamma (sub@Subtractive{}) goalTy =
  case goalTy of
    (ForallTyS _ binders constraints (ProdTy t1 t2)) -> do
      (e1, delta1, subst1) <- synthesiseInner decls True sub gamma [] (ForallTyS nullSpanNoFile binders constraints t1)
      (e2, delta2, subst2) <- synthesiseInner decls True sub delta1 [] (ForallTyS nullSpanNoFile binders constraints t2)
      subst <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
      return (makePair t1 t2 e1 e2, delta2, subst)
    _ -> none
pairIntroHelper decls gamma (add@(Additive mode)) goalTy =
  case goalTy of
    (ForallTyS _ binders constraints (ProdTy t1 t2)) -> do
      (e1, delta1, subst1) <- synthesiseInner decls True add gamma [] (ForallTyS nullSpanNoFile binders constraints t1)

      gamma' <- case mode of
                  Default     -> return gamma              -- no-prunes
                  Alternative -> ctxtSubtract gamma delta1 -- pruning

      (e2, delta2, subst2) <- synthesiseInner decls True add gamma' [] (ForallTyS nullSpanNoFile binders constraints t2)
      delta3 <- maybeToSynthesiser $ ctxtAdd delta1 delta2
      subst <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
      return (makePair t1 t2 e1 e2, delta3, subst)
    _ -> none


sumIntroHelper :: (?globals :: Globals)
  => Ctxt DataDecl -> Ctxt Assumption -> ResourceScheme AltOrDefault -> TypeScheme -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
sumIntroHelper decls gamma resourceScheme goalTy =
  case goalTy of
    (ForallTyS _ binders constraints (SumTy t1 t2)) -> do
      try
        (do
            (e1, delta1, subst1) <- synthesiseInner decls True resourceScheme gamma [] (ForallTyS nullSpanNoFile binders constraints t1)
            return (makeEitherLeft t1 t2 e1, delta1, subst1)

        )
        (do
            (e2, delta2, subst2) <- synthesiseInner decls True resourceScheme gamma [] (ForallTyS nullSpanNoFile binders constraints t2)
            return (makeEitherRight t1 t2 e2, delta2, subst2)

        )
    _ -> none


unitElimHelper :: (?globals :: Globals)
  => Ctxt DataDecl
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
unitElimHelper decls left [] _ _ _ = none
unitElimHelper decls left (var@(x,a):right) gamma (sub@Subtractive{}) goalTy = do
  (unitElimHelper decls (var:left) right gamma sub goalTy) `try`
    case (getAssumptionType a) of
      (TyCon (internalName -> "()")) -> do
        (e, delta, subst) <- synthesiseInner decls True sub gamma (left ++ right) goalTy
        return (makeUnitElim x e goalTy, delta, subst)
      _ -> none

unitElimHelper decls left (var@(x,a):right) gamma (add@Additive{}) goalTy =
  (unitElimHelper decls (var:left) right gamma add goalTy) `try`
    case (getAssumptionType a) of
      (TyCon (internalName -> "()")) -> do
        (e, delta, subst) <- synthesiseInner decls True add gamma (left ++ right) goalTy
        return (makeUnitElim x e goalTy, (var:delta), subst)
      _ -> none


sumElimHelper :: (?globals :: Globals)
  => Ctxt DataDecl
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> ResourceScheme AltOrDefault
  -> TypeScheme
  -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
sumElimHelper decls left [] _ _ _ = none
sumElimHelper decls left (var@(x, a):right) gamma (sub@Subtractive{}) goalTy =
  (sumElimHelper decls (var:left) right gamma sub goalTy) `try`
  let omega = left ++ right in do
  (canUse, omega', t) <- useVar var omega sub
  case (canUse, t) of
    (True, SumTy t1 t2) -> do
      l <- freshIdentifier
      r <- freshIdentifier
      let (gamma', omega'') = bindToContext (l, Linear t1) gamma omega' (isLAsync t1)
      let (gamma'', omega''') = bindToContext (r, Linear t2) gamma omega' (isLAsync t2)
      (e1, delta1, subst1) <- synthesiseInner decls True sub gamma' omega'' goalTy
      (e2, delta2, subst2) <- synthesiseInner decls True sub gamma'' omega''' goalTy
      subst <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
      case (lookup l delta1, lookup r delta2) of
          (Nothing, Nothing) -> do
            -- Both `l` and `r` were used in `delta1` and `delta2` respectively
            delta3 <- ctxtMerge CMeet delta1 delta2
            return (makeCase t1 t2 x l r e1 e2, delta3, subst)
          _ -> none
    _ -> none

sumElimHelper decls left (var@(x, a):right) gamma (add@(Additive mode)) goalTy =
  (sumElimHelper decls (var:left) right gamma add goalTy) `try`
  let omega = (var:left) ++ right in do
  (canUse, omega', t) <- useVar var omega add
  case (canUse, t) of
    (True, SumTy t1 t2) -> do
      l <- freshIdentifier
      r <- freshIdentifier
      omega1 <- ctxtSubtract omega omega'
      let (gamma', omega1') = bindToContext (l, Linear t1) gamma omega1 (isLAsync t1)
      let (gamma'', omega1'') = bindToContext (r, Linear t2) gamma omega1 (isLAsync t2)
      (e1, delta1, subst1) <- synthesiseInner decls True add gamma' omega1' goalTy
      (e2, delta2, subst2) <- synthesiseInner decls True add gamma'' omega1'' goalTy
      subst <- conv $ combineSubstitutions nullSpanNoFile subst1 subst2
      case (lookupAndCutout l delta1, lookupAndCutout r delta2) of
          (Just (delta1', Linear _), Just (delta2', Linear _)) -> do
            delta3 <- ctxtMerge CJoin delta1' delta2'
            delta3' <- maybeToSynthesiser $ ctxtAdd omega' delta3
            return (makeCase t1 t2 x l r e1 e2, delta3', subst)
          _ -> none
    _ -> none



synthesiseInner :: (?globals :: Globals)
           => Ctxt DataDecl      -- ADT Definitions
           -> Bool                 -- whether a function is allowed at this point
           -> ResourceScheme AltOrDefault      -- whether the synthesis is in additive mode or not
           -> Ctxt Assumption    -- (unfocused) free variables
           -> Ctxt Assumption    -- focused variables
           -> TypeScheme           -- type from which to synthesise
           -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)

synthesiseInner decls allowLam resourceScheme gamma omega goalTy@(ForallTyS _ binders _ goalTy') = do
  debugM "synthDebug" $ "Synth inner with gamma = " ++ pretty gamma ++ ", and omega = "
                      ++ pretty omega ++ ", for goal = " ++ pretty goalTy
                      ++ ", isRAsync goalTy = " ++ show (isRAsync goalTy')
                      ++ ", isAtomic goalTy = " ++ show (isAtomic goalTy')

  case (isRAsync goalTy', omega) of
    (True, omega) ->
      -- Right Async : Decompose goalTy until synchronous
      absHelper decls gamma omega allowLam resourceScheme goalTy `try` none
    (False, omega@(x:xs)) ->
      -- Left Async : Decompose assumptions until they are synchronous (eliminators on assumptions)
      unboxHelper decls [] omega gamma resourceScheme goalTy
      `try`
      pairElimHelper decls [] omega gamma resourceScheme goalTy
      `try`
      sumElimHelper decls [] omega gamma resourceScheme goalTy
      `try`
      unitElimHelper decls [] omega gamma resourceScheme goalTy
    (False, []) ->
      (if not (isAtomic goalTy') then
          -- Right Sync : Focus on goalTy when goalTy is not atomic
          sumIntroHelper decls gamma resourceScheme goalTy
          `try`
          pairIntroHelper decls gamma resourceScheme goalTy
          `try`
          boxHelper decls gamma resourceScheme goalTy
          `try`
          unitIntroHelper decls gamma resourceScheme goalTy
       else none)
       -- Or can always try to do left sync:
       `try` (do
            -- Transition to synchronous (focused) search
            -- Left Sync: App rule + Init rules
            varHelper decls [] gamma resourceScheme goalTy
            `try`
            appHelper decls [] gamma resourceScheme goalTy)

synthesise :: (?globals :: Globals)
           => Ctxt DataDecl      -- ADT Definitions
           -> Bool                 -- whether a function is allowed at this point
           -> ResourceScheme AltOrDefault      -- whether the synthesis is in additive mode or not
           -> Ctxt Assumption    -- (unfocused) free variables
           -> Ctxt Assumption    -- focused variables
           -> TypeScheme           -- type from which to synthesise
           -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
synthesise decls allowLam resourceScheme gamma omega goalTy = do
  result@(expr, ctxt, subst) <- synthesiseInner decls allowLam resourceScheme gamma omega goalTy
  case resourceScheme of
    Subtractive{} -> do
      -- All linear variables should be gone
      -- and all graded should approximate 0
      consumed <- mapM (\(id, a) ->
                    case a of
                      Linear{} -> return False;
                      Discharged _ grade -> do
                        (kind, _) <-  conv $ inferCoeffectType nullSpan grade
                        conv $ addConstraint (ApproximatedBy nullSpanNoFile (CZero kind) grade kind)
                        solve) ctxt
      if and consumed
        then return result
        else none

    -- All linear variables should have been used
    -- and all graded assumptions should have usages which approximate their original assumption
    Additive{} -> do
      consumed <- mapM (\(id, a) ->
                    case lookup id gamma of
                      Just (Linear{}) -> return True;
                      Just (Discharged _ grade) ->
                        case a of
                          Discharged _ grade' -> do
                            (kind, _) <- conv $ inferCoeffectType nullSpan grade
                            conv $ addConstraint (ApproximatedBy nullSpanNoFile grade' grade kind)
                            solve
                          _ -> return False
                      Nothing -> return False) ctxt
      if and consumed
        then return result
        else none

-- Run from the checker
synthesiseProgram :: (?globals :: Globals)
           => Ctxt DataDecl      -- ADT Definitions
           -> ResourceScheme AltOrDefault       -- whether the synthesis is in additive mode or not
           -> Ctxt Assumption    -- (unfocused) free variables
           -> Ctxt Assumption    -- focused variables
           -> TypeScheme           -- type from which to synthesise
           -> CheckerState
           -> IO [(Expr () Type, Ctxt Assumption, Substitution)]
synthesiseProgram decls resourceScheme gamma omega goalTy checkerState = do
  start <- liftIO $ Clock.getTime Clock.Monotonic
  -- %%
  let synRes = synthesise decls True resourceScheme gamma omega goalTy
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
sizeOfPred (Impl p1 p2) = 1 + (sizeOfPred p1) + (sizeOfPred p2)
sizeOfPred (Con c) = sizeOfConstraint c
sizeOfPred (NegPred p) = 1 + (sizeOfPred p)
sizeOfPred (Exists _ _ p) = 1 + (sizeOfPred p)
sizeOfPred (Forall _ _ p) = 1 + (sizeOfPred p)

sizeOfConstraint :: Constraint -> Integer
sizeOfConstraint (Eq _ c1 c2 _) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfConstraint (Neq _ c1 c2 _) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfConstraint (ApproximatedBy _ c1 c2 _) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfConstraint (Lub _ c1 c2 c3 _) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2) + (sizeOfCoeffect c3)
sizeOfConstraint (NonZeroPromotableTo _ _ c _) = 1 + (sizeOfCoeffect c)
sizeOfConstraint (Lt _ c1 c2) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfConstraint (Gt _ c1 c2) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfConstraint (LtEq _ c1 c2) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfConstraint (GtEq _ c1 c2) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)

sizeOfCoeffect :: Coeffect -> Integer
sizeOfCoeffect (CPlus c1 c2) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfCoeffect (CTimes c1 c2) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfCoeffect (CMinus c1 c2) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfCoeffect (CMeet c1 c2) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfCoeffect (CJoin c1 c2) = 1 + (sizeOfCoeffect c1) + (sizeOfCoeffect c2)
sizeOfCoeffect (CZero _) = 0
sizeOfCoeffect (COne _) = 0
sizeOfCoeffect (CVar _) = 0
sizeOfCoeffect _ = 0

--------------------------------
-- Testing code

topLevel :: (?globals :: Globals) => TypeScheme -> ResourceScheme AltOrDefault -> Synthesiser (Expr () Type, Ctxt Assumption, Substitution)
topLevel ts@(ForallTyS _ binders constraints ty) resourceScheme = do
  conv $ State.modify (\st -> st { tyVarContext = map (\(n, c) -> (n, (c, ForallQ))) binders})
  synthesise [] True resourceScheme [] [] ts

testGlobals :: Globals
testGlobals = mempty
  { globalsNoColors = Just True
  , globalsSuppressInfos = Just True
  , globalsTesting = Just True
  }

testSyn :: Bool -> IO ()
testSyn useReprint =
  let ty =
--        FunTy Nothing (Box (CInterval (CNat 2) (CNat 3)) (TyVar $ mkId "b") ) (FunTy Nothing (SumTy (TyVar $ mkId "a") (TyVar $ mkId "c")) (SumTy (ProdTy (TyVar $ mkId "a") (Box (CInterval (CNat 2) (CNat 2)) (TyVar $ mkId "b") )) (ProdTy (TyVar $ mkId "c") (Box (CInterval (CNat 3) (CNat 3)) (TyVar $ mkId "b") ))))
--        FunTy Nothing (TyVar $ mkId "a") (SumTy (TyVar $ mkId "b") (TyVar $ mkId "a"))
        FunTy Nothing (Box (CNat 3) (TyVar $ mkId "a")) (FunTy Nothing (Box (CNat 6) (TyVar $ mkId "b") ) (Box (CNat 3) (ProdTy (ProdTy (TyVar $ mkId "b") (TyVar $ mkId "b")) (TyVar $ mkId "a")) ))
--        FunTy Nothing (Box (CNat 2) (TyVar $ mkId "a")) (ProdTy (TyVar $ mkId "a") (TyVar $ mkId "a"))
--        FunTy Nothing (FunTy Nothing (TyVar $ mkId "a") (FunTy Nothing (TyVar $ mkId "b") (TyVar $ mkId "c"))) (FunTy Nothing (TyVar $ mkId "b") (FunTy Nothing (TyVar $ mkId "a") (TyVar $ mkId "c")))
--        FunTy Nothing (TyVar $ mkId "a") (TyVar $ mkId "a")
--        FunTy Nothing (Box (CNat 2) (TyVar $ mkId "a")) (ProdTy (TyVar $ mkId "a") (TyVar $ mkId "a"))
        in
    let ts = (ForallTyS nullSpanNoFile [(mkId "a", KType), (mkId "b", KType), (mkId "c", KType)] [] ty) in
    let ?globals = testGlobals in do
     -- State.modify (\st -> st { tyVarContext = map (\(n, c) -> (n, (c, ForallQ))) [(mkId "a", KType)]})
    let res = testOutput $ topLevel ts (Subtractive Default) in -- [(mkId "y", Linear (TyVar $ mkId "b")), (mkId "x", Linear (TyVar $ mkId "a"))] [] ty
        if length res == 0
        then  (putStrLn "No inhabitants found.")
        else  (forM_ res (\(ast, _, sub) -> putStrLn $
                           (if useReprint then pretty (reprintAsDef (mkId "f") ts ast) else pretty ast) ++ "\n" ++ (show sub) ))

testOutput :: Synthesiser a -> [a]
testOutput res =
  rights $ map fst $ fst $ unsafePerformIO $ runStateT (runSynthesiser res initState) mempty

--testData :: Synthesiser a -> SynthesisData
--testData res =
--  snd $ unsafePerformIO $ runSynthesiser res initState
