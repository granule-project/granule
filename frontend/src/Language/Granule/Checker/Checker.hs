{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}

{-# options_ghc -fno-warn-incomplete-uni-patterns -Wno-deprecations #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant <$>" #-}

-- | Core type checker
module Language.Granule.Checker.Checker where

import Control.Arrow (second)
import Control.Monad.State.Strict
import Control.Monad.Except (throwError)
import Data.List.NonEmpty (NonEmpty(..))
import Data.List (isPrefixOf)
import Data.List.Split (splitPlaces)
import qualified Data.List.NonEmpty as NonEmpty (toList)
import Data.Maybe
import qualified Data.Text as T

import Language.Granule.Checker.CoeffectsTypeConverter
import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Constraints.SymbolicGrades
import Language.Granule.Checker.Coeffects
import Language.Granule.Checker.Constraints
import Language.Granule.Checker.DataTypes (registerTypeConstructor, registerDataConstructors)
import Language.Granule.Checker.Exhaustivity
import Language.Granule.Checker.Effects
import Language.Granule.Checker.Ghost
import Language.Granule.Checker.Monad
import Language.Granule.Checker.NameClash
import Language.Granule.Checker.Patterns
import Language.Granule.Checker.Predicates
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Checker.Simplifier
import Language.Granule.Checker.Kinding
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Types
import Language.Granule.Checker.TypeAliases
import Language.Granule.Checker.Variables
import Language.Granule.Context

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Helpers (hasHole, freeVars)
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pattern (Pattern(..))
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type hiding (Polarity)

import Language.Granule.Synthesis.Deriving
import Language.Granule.Synthesis.Splitting

import Language.Granule.Utils

-- Checking (top-level)
check :: (?globals :: Globals)
  => AST () ()
  -> IO (Either (NonEmpty CheckerError) (AST () Type, [Def () ()]))
check ast@(AST _ _ _ hidden _) = do
  evalChecker (initState { allHiddenNames = hidden }) $ (do
      ast@(AST dataDecls defs imports hidden name) <- return $ replaceTypeAliases ast
      _    <- checkNameClashes Primitives.typeConstructors Primitives.dataTypes ast Primitives.builtinsParsed
      debugHeadingM "Register type constructors"
      _    <- runAll registerTypeConstructor  (Primitives.dataTypes <> dataDecls)
      debugHeadingM "Register data constructors"
      _    <- runAll registerDataConstructors (Primitives.dataTypes <> dataDecls)
      defs <- runAll kindCheckDef defs
      let defCtxt = map (\(Def _ name _ _ _ tys) -> (name, tys)) defs
      defs' <- runAll (checkDef defCtxt) defs
      -- Add on any definitions computed by the type checker (derived)
      st <- get
      let derivedDefs = map (snd . snd) (derivedDefinitions st)
      pure $ (AST dataDecls defs' imports hidden name, derivedDefs))

-- Synthing the type of a single expression in the context of an asy
synthExprInIsolation :: (?globals :: Globals)
  => AST () ()
  -> Expr () ()
  -> IO (Either (NonEmpty CheckerError) (Either (TypeScheme , [Def () ()]) Type))
synthExprInIsolation ast@(AST dataDecls defs imports hidden name) expr =
  evalChecker (initState { allHiddenNames = hidden }) $ do
      _    <- checkNameClashes Primitives.typeConstructors Primitives.dataTypes ast Primitives.builtinsParsed
      _    <- runAll registerTypeConstructor (Primitives.dataTypes ++ dataDecls)
      _    <- runAll registerDataConstructors (Primitives.dataTypes ++ dataDecls)
      defs <- runAll kindCheckDef defs

      let defCtxt = map (\(Def _ name _ _ _ tys) -> (name, tys)) defs

      -- also check the defs
      defs <- runAll (checkDef defCtxt) defs

      -- Since we need to return a type scheme, have a look first
      -- for top-level identifiers with their schemes
      case expr of
        -- Lookup in data constructors
        (Val s _ _ (Constr _ c [])) -> do
          mConstructor <- lookupDataConstructor s c
          case mConstructor of
            Just (tySch, _, _) -> return $ Left (tySch, [])
            Nothing -> do
              st <- get
              -- Or see if this is a kind constructors
              case lookup c (typeConstructors st) of
                Just (k, _, _) -> return $ Right k
                Nothing -> throw UnboundDataConstructor{ errLoc = s, errId = c }

        -- Lookup in definitions
        (Val s _ _ (Var _ x)) -> do
          case lookup x (defCtxt <> Primitives.builtins) of
            Just tyScheme -> return $ Left (tyScheme, [])
            Nothing -> throw UnboundVariableError{ errLoc = s, errId = x }

        -- Otherwise, do synth
        _ -> do
          modify' $ \st -> st
            { predicateStack = []
            , guardPredicates = [[]]
            , tyVarContext = []
            , futureFrame = []
            , uniqueVarIdCounterMap = mempty
            , wantedTypeConstraints = []
            }
          (ty, _, subst, _) <- synthExpr defCtxt [] Positive expr
          -- Solve the generated constraints
          checkerState <- get
          tyVarContext' <- substitute subst (tyVarContext checkerState)
          put $ checkerState { tyVarContext = tyVarContext' }

          -- Deal with additional constraints (due to session mostly)
          let wantedTcs = wantedTypeConstraints checkerState
          wantedTcs <- mapM (substitute subst) wantedTcs
          dischargedTypeConstraints (getSpan expr) [] wantedTcs

          let predicate = Conj $ predicateStack checkerState
          predicate <- substitute subst predicate
          solveConstraints predicate (getSpan expr) (mkId "grepl")


          let derivedDefs = map (snd . snd) (derivedDefinitions checkerState)

          -- Apply the outcoming substitution
          ty' <- substitute subst ty
          binders <- tyVarContextToTypeSchemeVars (freeVars ty')
          return $ Left (Forall nullSpanNoFile binders [] ty', derivedDefs)


checkDef :: (?globals :: Globals)
         => Ctxt TypeScheme  -- context of top-level definitions
         -> Def () ()        -- definition
         -> Checker (Def () Type)
checkDef defCtxt (Def s defName rf spec el@(EquationList _ _ _ equations)
                 tys@(Forall s_t foralls constraints ty)) = do
    -- duplicate forall bindings
    case duplicates (map (sourceName . fst) foralls) of
      [] -> pure ()
      (d:ds) -> throwError $ fmap (DuplicateBindingError s_t) (d :| ds)

    -- _ <- checkSpec defCtxt spec ty

    -- Clean up knowledge shared between equations of a definition
    modify (\st -> st { currentDef = (Just defName, spec)
                      , guardPredicates = [[]]
                      , patternConsumption = initialisePatternConsumptions equations } )

    elaboratedEquations :: [Equation () Type] <- runAll elaborateEquation equations

    checkGuardsForExhaustivity s defName ty equations
    let el' = el { equations = elaboratedEquations }
    pure $ Def s defName rf Nothing el' tys
  where
    elaborateEquation :: Equation () () -> Checker (Equation () Type)
    elaborateEquation equation = do
      -- Erase the solver predicate between equations
        modify' $ \st -> st
            { predicateStack = []
            , guardPredicates = [[]]
            , tyVarContext = []
            , futureFrame = []
            , uniqueVarIdCounterMap = mempty
            , wantedTypeConstraints = []
            }
        debugM "elaborateEquation" ("checkEquation with type scheme " <> pretty tys)
        (elaboratedEq, providedTcs, subst) <- checkEquation defCtxt defName equation tys
        debugM "elaborateEquation" "checkEquation done"

        -- Solve the generated constraints
        checkerState <- get
        tyVarContext' <- substitute subst (tyVarContext checkerState)
        put $ checkerState { tyVarContext = tyVarContext' }

        -- Deal with additional constraints (due to session mostly)
        let wantedTcs = wantedTypeConstraints checkerState
        wantedTcs <- mapM (substitute subst) wantedTcs
        dischargedTypeConstraints s providedTcs wantedTcs

        -- Apply the final substitution to the outcoming predicate
        -- and run the solver
        let predicate = Conj $ predicateStack checkerState
        debugM "elaborateEquation" ("solveEq with final substitution = " <> pretty subst)
        predicate <- substitute subst predicate
        solveConstraints predicate (getSpan equation) defName

        -- Apply the final substitution to head of the guard predicate stack too
        st <- get
        debugM "guardPredicatePreSubst" (pretty (guardPredicates st))
        modifyM (\st ->
          case guardPredicates st of
            [] -> return st
            [guardPred] -> do
                guardPred' <- mapM (\((ctxt, pred), sp) -> do
                  ctxt' <- substitute subst ctxt
                  pred' <- substitute subst pred
                  return ((ctxt', pred'), sp)) guardPred
                return (st { guardPredicates = [guardPred'] })
            guardPred -> do
              error $ "Granule internal bug: PLEASE REPORT!\n"
                  ++  "Final guard predicate stack is not a singleton: "
                  ++  show guardPred)

        debugM "elaborateEquation" "solveEq done"

        checkGuardsForImpossibility s defName []

        pure elaboratedEq

-- checkSpec :: (?globals :: Globals) =>
checkSpec ::
     Ctxt TypeScheme
  -> Maybe (Spec () ())
  -> Type
  -> Checker (Maybe (Spec () Type))
checkSpec defCtxt Nothing defTy = return Nothing
checkSpec defCtxt (Just (Spec span refactored examples components)) defTy = undefined -- do

  -- elaboratedExamples :: [Example () Type] <- runAll elaborateExample examples

  -- forM_ components (\(ident, _) -> do
  --     case lookup ident defCtxt of
  --         Just _ -> return ()
  --         _ -> throw UnboundVariableError{ errLoc = span, errId = ident})

  -- return (Just (Spec span refactored elaboratedExamples components))

  -- where
  --   elaborateExample :: Example () () -> Checker (Example () Type)
  --   elaborateExample (Example input output) = do
  --     (_, _, elaboratedInput) <- checkExpr defCtxt [] Positive True (resultType defTy) input
  --     (_, _, elaboratedOutput) <- checkExpr defCtxt [] Positive True (resultType defTy) output
  --     return (Example elaboratedInput elaboratedOutput)





checkEquation :: (?globals :: Globals) =>
     Ctxt TypeScheme -- context of top-level definitions
  -> Id              -- Name of the definition
  -> Equation () ()  -- Equation
  -> TypeScheme      -- Type scheme
  -> Checker (Equation () Type, [Type], Substitution)
                     -- Returns triple of elaborated equation syntax
                     --                   list of remaining type constraints (non-graded things)
                    --                    final substitution

checkEquation defCtxt id (Equation s name () rf pats expr) tys@(Forall _ binders constraints defTy) = do
  -- Check that the lhs doesn't introduce any duplicate binders
  duplicateBinderCheck s pats

  -- Initialize the type context with the type variable binders in scope from the signature
  binders' <- refineBinderQuantification binders defTy
  modify $ \st -> st { tyVarContext = binders' }

  -- Create conjunct to capture the pattern constraints
  newConjunct

  providedTypeConstraints <- enforceConstraints s constraints

  -- Build the binding context for the branch pattern
  st <- get
  (patternGam, tau, localVars, subst, elaborated_pats, consumptions) <-
     ctxtFromTypedPatterns s InFunctionEquation defTy pats (patternConsumption st)

  -- Update the consumption information
  modify (\st -> st { patternConsumption =
                         zipWith joinConsumption consumptions (patternConsumption st) } )

  -- Create conjunct to capture the body expression constraints
  newConjunct

  --tau' <- substitute subst tau

  reportM $ "Body type is " <> pretty tau
  --reportM $ "Body type with substitution is " <> pretty tau'
  st <- get
  reportM $ "Predicate after type checking pattern is " <> pretty (predicateStack st)

  -- The type of the equation, after substitution.
  equationTy' <- substitute subst defTy
  -- Substitute into the body to handle type annotations
  expr        <- substitute subst expr
  let splittingTy = calculateSplittingTy patternGam equationTy'

  -- Store the equation type in the state in case it is needed when splitting
  -- on a hole.
  modify (\st -> st { splittingTy = Just splittingTy})

  --patternGam <- substitute subst patternGam
  debugM "context in checkEquation 1" $ (show patternGam)

  -- Introduce ambient coeffect
  combinedGam <-
    if SecurityLevels `elem` globalsExtensions ?globals
    then ghostVariableContextMeet $ patternGam <> freshGhostVariableContext
    else return patternGam

  -- Check the body
  (localGam, subst', elaboratedExpr) <-
       checkExpr defCtxt combinedGam Positive True tau expr

  case checkLinearity patternGam localGam of
    [] -> do
      localGam <- substitute subst localGam
      -- Check that our consumption context matches the binding
      subst0 <- if NoTopLevelApprox `elem` globalsExtensions ?globals
        then ctxtEquals s localGam combinedGam
        else do
          ctxtApprox s localGam combinedGam


      -- Create elaborated equation
      subst'' <- combineManySubstitutions s [subst0, subst, subst']
      let elab = Equation s name defTy rf elaborated_pats elaboratedExpr

      elab' <- substitute subst'' elab

      -- Conclude the implication
      concludeImplication s localVars


      st <- get
      reportMsep
      reportM $ "Final state of predicate: " <> pretty (predicateStack st)
      reportMsep


      return (elab', providedTypeConstraints, subst'')

    -- Anything that was bound in the pattern but not used up
    (p:ps) -> illLinearityMismatch s (p:|ps)

  where


    -- TODO: Rewrite this function so it's less confusing as to what info is being
    --       passed to the splitter here.

    -- Given a context of patterns, and the type of the equation, uses
    -- these to calculate a type which represents the arguments which are to
    -- be split on by deconstructing patterns into their constituent patterns

    -- e.g. Given a pattern: Cons x xs
    --      and a type:      Vec (n+1) t -> Vec n t
    --      returns:         t -> Vec n t -> Vec n t

    -- i.e. If Vec (n+1) t -> Vec n t is the type of the equation
    -- and the pattern we're splitting on is (Cons x xs) then we
    -- take the types of each sub-pattern of Cons:
    --      x  : t
    --      xs : Vec n t
    -- and use these to build a function from these sub-patterns to
    -- the return type of our input type.

    calculateSplittingTy :: [(Id, Assumption)] -> Type -> Type
    calculateSplittingTy patternGam ty =
      case patternGam of
        [] -> ty
        (_:_) ->
          let patternArities = map patternArity pats
              patternFunTys = map (map assumptionToType) (splitPlaces patternArities patternGam)
          in replaceParameters patternFunTys ty

    -- Computes how many arguments a pattern has.
    -- e.g. Cons x xs --> 2
    patternArity :: Pattern a -> Integer
    patternArity (PBox _ _ _ p) = patternArity p
    patternArity (PConstr _ _ _ _ _ ps) = sum (map patternArity ps)
    patternArity _ = 1

    replaceParameters :: [[Type]] -> Type -> Type
    replaceParameters [] ty = ty
    replaceParameters ([]:tss) (FunTy id grade _ ty) = replaceParameters tss ty
    replaceParameters ((t:ts):tss) ty =
      FunTy Nothing Nothing t (replaceParameters (ts:tss) ty)
    replaceParameters _ t = error $ "Expecting function type: " <> pretty t

    -- Convert an id+assumption to a type.
    assumptionToType :: (Id, Assumption) -> Type
    assumptionToType (_, Linear t) = t
    assumptionToType (_, Discharged t _) = t
    assumptionToType (_, Ghost _) = ghostType

-- Polarities are used to understand when a type is
-- `expected` vs. `actual` (i.e., for error messages)
data Polarity = Positive | Negative deriving Show

flipPol :: Polarity -> Polarity
flipPol Positive = Negative
flipPol Negative = Positive

-- Type check an expression

--  `checkExpr defs gam t expr` computes `Just delta`
--  if the expression type checks to `t` in context `gam`:
--  where `delta` gives the post-computation context for expr
--  (which explains the exact coeffect demands)
--  or `Nothing` if the typing does not match.

checkExpr :: (?globals :: Globals)
          => Ctxt TypeScheme   -- context of top-level definitions
          -> Ctxt Assumption   -- local typing context
          -> Polarity         -- polarity of <= constraints
          -> Bool             -- whether we are top-level or not
          -> Type        -- type
          -> Expr () ()       -- expression
          -> Checker (Ctxt Assumption, Substitution, Expr () Type)

-- Hit an unfilled hole
checkExpr defs ctxt _ _ t (Hole s _ _ vars hints) = do
  debugM "checkExpr[Hole]" (pretty s <> " : " <> pretty t)

  st <- get
  let boundVariables = map fst $ filter (\ (id, _) -> sourceName id `elem` map sourceName vars) ctxt
  let unboundVariables = filter (\ x -> isNothing (lookup x ctxt)) vars

  -- elaborated hole
  let hexpr = Hole s () False vars hints
  let hindex = case hints of
        Just hints' -> fromMaybe 1 $ hIndex hints'
        _ -> 1

  case unboundVariables of
    (v:_) -> throw UnboundVariableError{ errLoc = s, errId = v }
    [] -> do

      -- Running in synthesis mode
      case globalsSynthesise ?globals of
        Just True -> do

          relevantConstructors <- do
            let snd3 (a, b, c) = b
                tripleToTup (a, b, c) = (a, b)
            st <- get
            let pats = map (second snd3) (typeConstructors st)
            mapM (\ (a, b) -> do
              dc <- mapM (lookupDataConstructor nullSpanNoFile) b
              let sd = zip (fromJust $ lookup a pats) (catMaybes dc)
              return (a, ctxtMap tripleToTup sd)) pats

          let holeVars = map (\id -> (id, id `elem` boundVariables)) (map fst ctxt)
          -- Check to see if this hole is something we are interested in
          case globalsHolePosition ?globals of
            -- Synth everything mode
            Nothing -> do
              throw $ HoleMessage s t ctxt (tyVarContext st) holeVars (Just (st, defs, currentDef st, hindex, hints, relevantConstructors)) [([], hexpr)]
            Just pos ->
              if spanContains pos s
              -- This is a hole we want to synth on
              then do
                throw $ HoleMessage s t ctxt (tyVarContext st) holeVars (Just (st, defs, currentDef st, hindex, hints, relevantConstructors)) [([], hexpr)]
                -- This is not a hole we want to synth on
              else
                throw $ HoleMessage s t ctxt (tyVarContext st) holeVars Nothing [([], hexpr)]


        _ -> do
              let pats = map (second snd3) (typeConstructors st)
              constructors <- mapM (\ (a, b) -> do
                  dc <- mapM (lookupDataConstructor s) b
                  let sd = zip (fromJust $ lookup a pats) (catMaybes dc)
                  return (a, sd)) pats
              (_, cases) <- generateCases s constructors ctxt boundVariables

              -- If we are in synthesise mode, also try to synthesise a
              -- term for each case split goal *if* this is also a hole
              -- of interest
              let casesWithHoles = zip (map fst cases) (repeat (Hole s () True [] Nothing))

              let holeVars = map (\id -> (id, id `elem` boundVariables)) (map fst ctxt)
              throw $ HoleMessage s t ctxt (tyVarContext st) holeVars Nothing casesWithHoles
            -- _ -> do
            --   let holeVars = map (\id -> (id, id `elem` boundVariables)) (map fst ctxt)
              -- throw $ HoleMessage s t ctxt (tyVarContext st) holeVars Nothing [([], hexpr)]

-- Checking of constants
checkExpr _ _ _ _ ty@(TyCon c) (Val s _ rf (NumInt n))   | internalName c == "Int" = do
  debugM "checkExpr[NumInt]" (pretty s <> " : " <> pretty ty)
  let elaborated = Val s ty rf (NumInt n)
  return (usedGhostVariableContext, [], elaborated)

checkExpr _ _ _ _ ty@(TyCon c) (Val s _ rf (NumFloat n)) | internalName c == "Float" = do
  debugM "checkExpr[NumFloat]" (pretty s <> " : " <> pretty ty)
  let elaborated = Val s ty rf (NumFloat n)
  return (usedGhostVariableContext, [], elaborated)

-- Differentially private floats
checkExpr _ _ _ _ ty@(TyCon c) (Val s _ rf (NumFloat n)) | internalName c == "DFloat" = do
  debugM "checkExpr[NumFloat-Dfloat]" (pretty s <> " : " <> pretty ty)
  let elaborated = Val s ty rf (NumFloat n)
  return (usedGhostVariableContext, [], elaborated)

checkExpr defs gam pol _ ty@(FunTy _ grade sig tau) (Val s _ rf (Abs _ p t e)) | usingExtension GradedBase = do
  debugM "checkExpr[FunTy-graded base]" (pretty s <> " : " <> pretty ty)
  -- If an explicit signature on the lambda was given, then check
  -- it confirms with the type being checked here

  (sig', subst1) <- case t of
    Nothing -> return (sig, [])
    Just sig' -> do
      (eqT, unifiedSigType, subst) <- lEqualTypes s sig sig'
      unless eqT $ throw TypeErrorConflictingExpected{ errLoc = s, tyExpected' = sig', tyExpected = sig }
      return (unifiedSigType, subst)

  newConjunct

  -- Get the type of the grade (if there is a grade)
  (gradeAndType, subst0) <-
      case grade of
          Nothing -> do
            one <- generatePolymorphicGrade1 s
            return (Just one, [])
          Just r -> do
            (t, subst0, _) <- synthKind s r
            return (Just (r, t), subst0)

  (bindings, localVars, subst, elaboratedP, _) <- ctxtFromTypedPattern' gradeAndType s InCase sig' p NotFull
  debugM "binding from lam" $ pretty bindings

  pIrrefutable <- isIrrefutable s sig' p
  if pIrrefutable then do
    -- Check the body in the extended context
    tau' <- substitute subst tau

    newConjunct

    (gam', subst2, elaboratedE) <- checkExpr defs (bindings <> gam) pol False tau' e
    -- Check linearity of locally bound variables
    case checkLinearity bindings gam' of
       [] -> do
          subst <- combineManySubstitutions s [subst, subst0, subst1, subst2]

          -- Locally we should have this property (as we are under a binder)
          subst' <- ctxtApprox s (gam' `intersectCtxts` bindings) bindings
          let elaborated = Val s ty rf (Abs ty elaboratedP t elaboratedE)

          substFinal <- combineSubstitutions s subst subst'
          concludeImplication s localVars

          return (gam' `subtractCtxt` bindings, substFinal, elaborated)

       (p:ps) -> illLinearityMismatch s (p:|ps)
  else throw RefutablePatternError{ errLoc = s, errPat = p }

checkExpr defs gam pol _ ty@(FunTy _ Nothing sig tau) (Val s _ rf (Abs _ p t e)) = do
  debugM "checkExpr[FunTy]" (pretty s <> " : " <> pretty ty)
  -- If an explicit signature on the lambda was given, then check
  -- it confirms with the type being checked here

  (sig', subst1) <- case t of
    Nothing -> return (sig, [])
    Just sig' -> do
      (eqT, unifiedSigType, subst) <- lEqualTypes s sig sig'
      unless eqT $ throw TypeErrorConflictingExpected{ errLoc = s, tyExpected' = sig', tyExpected = sig }
      return (unifiedSigType, subst)

  newConjunct

  (bindings, localVars, subst0, elaboratedP, _) <- ctxtFromTypedPattern s InCase sig' p NotFull

  pIrrefutable <- isIrrefutable s sig' p
  if pIrrefutable then do
    -- Check the body in the extended context
    tau' <- substitute subst0 tau

    newConjunct

    (gam', subst2, elaboratedE) <- checkExpr defs (bindings <> gam) pol False tau' e
    -- Check linearity of locally bound variables
    case checkLinearity bindings gam' of
       [] -> do


          -- Locally we should have this property (as we are under a binder)
          subst' <- ctxtApprox s (gam' `intersectCtxts` bindings) bindings

          let elaborated = Val s ty rf (Abs ty elaboratedP t elaboratedE)

          substFinal <- combineManySubstitutions s [subst', subst0, subst1, subst2]
          concludeImplication s localVars

          return (gam' `subtractCtxt` bindings, substFinal, elaborated)

       (p:ps) -> illLinearityMismatch s (p:|ps)
  else throw RefutablePatternError{ errLoc = s, errPat = p }

-- Capabilities
-- matches a pattern: `cap CapName carrier`
checkExpr defs gam pol topLevel tau
      (App s _ rf
        (App _ _ _
           (Val _ _ _ (Var _ (internalName -> "cap")))
           (Val _ _ _ (Constr _ capName _)))
        carrier) = do

  -- Do we have this capabillity?
  case lookup capName Primitives.capabilities of
    Nothing -> throw UnboundVariableError{ errLoc = s, errId = capName }
    Just ty -> do
      -- Type the capability as a box thing
      (outContext, subst, _) <- checkExpr defs gam pol False (Box (TySet Normal [TyCon capName]) (TyCon $ mkId "()")) carrier
      (eq, _, subst') <- equalTypes s ty tau
      if eq
        then do
          -- elaborate just to a variable application
          let elab = Val s ty rf (Var ty (mkId $ "cap." <> internalName capName))
          substFinal <- combineSubstitutions s subst subst'
          return (outContext, substFinal, elab)
        else
           throw $ TypeError { errLoc = s, tyExpected = tau, tyActual = ty }


-- Application special case for built-in 'scale'
-- TODO: needs more thought
checkExpr defs gam pol topLevel tau
          (App s _ rf (App s' _ rf' (Val s'' _ rf'' (Var _ v)) (Val s3 _ rf3 (NumFloat x))) e) | internalName v == "scale" = do
    debugM "checkExpr[Scale]" (pretty s <> " : " <> pretty tau)
    let floatTy = TyCon $ mkId "DFloat"

    (eq, _, subst) <- equalTypes s floatTy tau
    if eq then do
      -- Type check the argument
      (gam, subst', elab) <- checkExpr defs gam pol topLevel (Box (TyRational (toRational x)) floatTy) e

      subst'' <- combineSubstitutions s subst subst'

      -- Create elborated AST
      let scaleTy = FunTy Nothing Nothing floatTy
                      (FunTy Nothing Nothing (Box (TyRational (toRational x)) floatTy) floatTy)
      let elab' = App s floatTy rf
                    (App s' scaleTy rf' (Val s'' floatTy rf'' (Var floatTy v)) (Val s3 floatTy rf3 (NumFloat x))) elab

      return (gam, subst'', elab')
      else
        throw $ TypeError { errLoc = s, tyExpected = TyCon $ mkId "DFloat", tyActual = tau }

-- Application checking
checkExpr defs gam pol topLevel tau (App s a rf e1 e2) | (usingExtension GradedBase) = do
  debugM "checkExpr[App]-gradedBase" (pretty s <> " : " <> pretty tau)

-- GRADED BASE
--
--      G1 |- e1 => a %r -> b    G2 |- e2 <= a
--  -------------------------------------------- app
--      G1 + r * G2 |- e1 e2 <= b
--
--  The moding here, with synthesis for e1, is because we need
--  to know the grade `r`.

  -- Syntheise type of function
  (tau', gam, subst, elab) <- synthExpr defs gam pol (App s a rf e1 e2)
  -- Check the return types match
  (eqT, _, substTy) <- equalTypes s tau tau'
  unless eqT $ throw TypeError{ errLoc = s, tyExpected = tau, tyActual = tau' }

  return (gam, subst, elab)

-- Graded base application
checkExpr defs gam pol topLevel tau (App s _ rf e1 e2) | not (usingExtension GradedBase) = do
    debugM "checkExpr[App]" (pretty s <> " : " <> pretty tau)
    (argTy, gam2, subst2, elaboratedR) <- synthExpr defs gam pol e2

    funTy <- substitute subst2 (FunTy Nothing Nothing argTy tau)
    (gam1, subst1, elaboratedL) <- checkExpr defs gam pol topLevel funTy e1

    gam <- ctxtPlus s gam1 gam2

    subst <- combineSubstitutions s subst1 subst2
    let elaborated = App s tau rf elaboratedL elaboratedR
    return (gam, subst, elaborated)

{-

[G] |- e : t
 ---------------------
[G]*r |- [e] : []_r t

-}

-- Promotion
checkExpr defs gam pol _ ty@(Box demand tau) (Val s _ rf (Promote _ e)) = do
    debugM "checkExpr[Box]" (pretty s <> " : " <> pretty ty)

    promotable <-
      if (CBN `elem` globalsExtensions ?globals)
        then return True
        -- In CBV mode, check we do not have a resource allocator here
        else return $ (not (resourceAllocator e)
        -- or see if we have turned on unsafe promotion
                   || (UnsafePromotion `elem` globalsExtensions ?globals))
    when (not promotable) (throw $ UnpromotableError{errLoc = s, errTy = ty})

    -- Checker the expression being promoted
    (gam', subst, elaboratedE) <- checkExpr defs gam pol False tau e

    -- Multiply the grades of all the used varibles here
    (gam'', subst') <-
      if hasHole e
        -- If we are promoting soemthing with a hole, then put all free variables in scope
        then ctxtMult s demand gam
        -- Otherwise we need to discharge only things that get used
        else ctxtMult s demand gam'

    substFinal <- combineManySubstitutions s [subst, subst']

    let elaborated = Val s ty rf (Promote tau elaboratedE)
    return (gam'', substFinal, elaborated)

-- Necessitation
checkExpr defs gam pol _ ty@(Star demand tau) (Val s _ rf (Nec _ e)) = do
    debugM "checkExpr[Star]" (pretty s <> " : " <> pretty ty)

    -- Checker the expression being necessitated
    (gam', subst, elaboratedE) <- checkExpr defs gam pol False tau e

    let elaborated = Val s ty rf (Nec tau elaboratedE)
    return (gam', subst, elaborated)

-- Check a case expression
checkExpr defs gam pol True tau (Case s _ rf guardExpr cases) = do
  debugM "checkExpr[Case]" (pretty s <> " : " <> pretty tau)
  -- Synthesise the type of the guardExpr
  (guardTy, guardGam, substG, elaboratedGuard) <- synthExpr defs gam pol guardExpr
  -- pushGuardContext guardGam

  -- Dependent / GADT pattern matches not allowed in a case
  ixed <- isIndexedType guardTy
  when ixed (throw $ CaseOnIndexedType s guardTy)

  -- (DEBUGGING) Determine if matching on type with more than one constructor
  isPolyShaped <- polyShaped guardTy

  -- if graded base
  scrutinee <-
    if usingExtension GradedBase
      then do
        s <- freshTyVarInContext (mkId "s") kcoeffect
        r <- freshTyVarInContext (mkId "scrutinee") (TyVar s)
        return (Just (TyVar r, TyVar s))
      else return Nothing

  newCaseFrame

  -- Check each of the branches
  branchCtxtsAndSubst <-
    forM cases $ \(pat_i, e_i) -> do

      -- Build the binding context for the branch pattern
      newConjunct
      (patternGam, eVars, subst, elaborated_pat_i, _) <-
        ctxtFromTypedPattern' scrutinee s InCase guardTy pat_i NotFull
      newConjunct

      -- Checking the case body
      tau' <- substitute subst tau
      patternGam <- substitute subst patternGam
      debugM "checkExpr[Case] patternGam" $ show patternGam
      -- combine ghost variables from pattern using converge/meet
      innerGam <-
        if (SecurityLevels `elem` globalsExtensions ?globals)
        then ghostVariableContextMeet $ patternGam <> gam
        else return $ patternGam <> gam
      (localGam, subst', elaborated_i) <- checkExpr defs innerGam pol False tau' e_i

      -- Converge with the outer ghost variable
      patternGam' <-
        if (SecurityLevels `elem` globalsExtensions ?globals)
        then ghostVariableContextMeet $ (mkId ".var.ghost", fromJust $ lookup (mkId ".var.ghost") gam) : patternGam
        else return patternGam
      -- Check that the use of locally bound variables matches their bound type
      subst'' <- ctxtApprox s (localGam `intersectCtxts` (patternGam)) (patternGam')

      -- Check linear use in anything Linear
      gamSoFar <- ctxtPlus s guardGam localGam
      case checkLinearity patternGam gamSoFar of
        -- Return the resulting computed context, without any of
        -- the variable bound in the pattern of this branch
        [] -> do
           substFinal <- combineManySubstitutions s [subst, subst', subst'']

           -- Conclude the implication
           concludeImplication (getSpan pat_i) eVars

           return (localGam `subtractCtxt` patternGam
                 , substFinal
                 , (elaborated_pat_i, elaborated_i))


        -- Anything that was bound in the pattern but not used correctly
        p:ps -> illLinearityMismatch s (p:|ps)

  let (branchCtxts, substs, elaboratedCases) = unzip3 branchCtxtsAndSubst

  -- All branches must be possible
  applySubstitutionsOnGuardPredicates s substs
  checkGuardsForImpossibility s (mkId "case") []

  -- Pop from stacks related to case
  -- _ <- popGuardContext
  popCaseFrame

  -- Find the upper-bound of the contexts
  (branchesGam, tyVars) <- foldM (\(ctxt, vars) ctxt' -> do
    (ctxt'', vars') <- joinCtxts s ctxt ctxt'
    return (ctxt'', vars ++ vars')) (head branchCtxts, []) (tail branchCtxts)

  -- Contract the outgoing context of the guard and the branches (joined)
  (g, substExtra) <-
    if usingExtension GradedBase
      then do
        -- r * guardGam + branchesGam
        (guardGam', subst) <- ctxtMult s (fst $ fromJust scrutinee) guardGam
        ctxtPlus s branchesGam guardGam' <.*> (return subst)

      else ctxtPlus s branchesGam guardGam <.*> return []

  subst <- combineManySubstitutions s (substG : substExtra : substs)

  -- Exisentially quantify any ty variables generated by joining contexts
  mapM_ (uncurry existentialTopLevel) tyVars

  let elaborated = Case s tau rf elaboratedGuard elaboratedCases
  return (g, subst, elaborated)

-- All other expressions must be checked using synthesis
checkExpr defs gam pol topLevel tau e = do
  debugM "checkExpr[*]" ("Term `" <> pretty e <> "` @ " <> pretty (getSpan e) <> " : " <> pretty tau)
  (tau', gam', subst', elaboratedE) <- synthExpr defs gam pol e

  -- Now to do a type equality on check type `tau` and synth type `tau'`
  (tyEq, _, subst) <-
        if topLevel && (not (NoTopLevelApprox `elem` globalsExtensions ?globals))
          -- If we are checking a top-level, then allow overapproximation
          then do
            debugM "** Compare for approximation " $ pretty tau' <> " <: " <> pretty tau
            lEqualTypesWithPolarity (getSpan e) SndIsSpec tau' tau
          else do
            debugM "** Compare for equality " $ pretty tau' <> " = " <> pretty tau
            equalTypesWithPolarity (getSpan e) SndIsSpec tau' tau

  debugM "Approximation/equality result" (show tyEq)
  if tyEq
    then do
      substFinal <- combineSubstitutions (getSpan e) subst subst'
      return (gam', substFinal, elaboratedE)
    else do
      case pol of
        Positive -> throw TypeError{ errLoc = getSpan e, tyExpected = tau , tyActual = tau' }
        Negative -> throw TypeError{ errLoc = getSpan e, tyExpected = tau', tyActual =  tau }

-- | Synthesise the 'Type' of expressions.
-- See <https://en.wikipedia.org/w/index.php?title=Bidirectional_type_checking&redirect=no>
synthExpr :: (?globals :: Globals)
          => Ctxt TypeScheme   -- ^ Context of top-level definitions
          -> Ctxt Assumption   -- ^ Local typing context
          -> Polarity          -- ^ Polarity of subgrading
          -> Expr () ()        -- ^ Expression
          -> Checker (Type, Ctxt Assumption, Substitution, Expr () Type)

-- Hit an unfilled hole
synthExpr _ ctxt _ (Hole s _ _ _ _) = do
  debugM "synthExpr[Hole]" (pretty s)
  throw $ InvalidHolePosition s

-- Literals can have their type easily synthesised
synthExpr _ _ _ (Val s _ rf (NumInt n))  = do
  debugM "synthExpr[NumInt]" (pretty s)
  let t = TyCon $ mkId "Int"
  return (t, usedGhostVariableContext, [], Val s t rf (NumInt n))

synthExpr _ _ _ (Val s _ rf (NumFloat n)) = do
  debugM "synthExpr[NumFloat]" (pretty s)
  let t = TyCon $ mkId "Float"
  return (t, usedGhostVariableContext, [], Val s t rf (NumFloat n))

synthExpr _ _ _ (Val s _ rf (CharLiteral c)) = do
  debugM "synthExpr[Char]" (pretty s)
  let t = TyCon $ mkId "Char"
  return (t, usedGhostVariableContext, [], Val s t rf (CharLiteral c))

synthExpr _ _ _ (Val s _ rf (StringLiteral c)) = do
  debugM "synthExpr[String]" (pretty s)
  let t = TyCon $ mkId "String"
  return (t, usedGhostVariableContext, [], Val s t rf (StringLiteral c))

-- Secret syntactic weakening
synthExpr defs gam pol
    (App s _ _ (Val _ _ _ (Var _ (sourceName -> "weak__"))) v@(Val _ _ _ (Var _ x))) = do
  debugM "synthExpr[weak__]" (pretty s)

  -- Check the variable is actually a graded variable
  case lookup x gam of
    Nothing ->         throw UnboundVariableError{ errLoc = s, errId = x }
    Just (Linear _) -> throw LinearityError{ errLoc = s, linearityMismatch = LinearUsedNonLinearly x }
    Just (Discharged _ r) -> do
      -- Infer the type of the variable
      (t, _, subst, elabE) <- synthExpr defs gam pol v

      -- Get the type of the grade
      (gradeType, subst', _) <- synthKind s r
      substF <- combineSubstitutions s subst subst'

      -- Return usage as 0 : gradeType
      return (t, weakenedGhostVariableContext <> [(x, Discharged t (TyGrade (Just gradeType) 0))], substF, elabE)
    Just (Ghost r) -> do
      -- Infer the type of the variable
      (t, _, subst, elabE) <- synthExpr defs gam pol v

      -- Get the type of the grade
      (gradeType, subst', _) <- synthKind s r
      substF <- combineSubstitutions s subst subst'

      debugM "secret weaken ghost" (pretty gradeType <> ", " <> pretty r)

      -- Return usage as 0 : gradeType
      return (t, weakenedGhostVariableContext <> [(x, Ghost (TyGrade (Just gradeType) 0))], substF, elabE)


-- Constructors
synthExpr _ gam _ (Val s _ rf (Constr _ c [])) = do
  debugM "synthExpr[Constr]" (pretty s <> " : " <> pretty c)
  -- Should be provided in the type checkers environment
  st <- get
  mConstructor <- lookupDataConstructor s c
  case mConstructor of
    Just (tySch, coercions, _) -> do
      -- Freshen the constructor
      -- (discarding any fresh type variables, info not needed here)

      (ty, _, constraints, coercions') <- freshPolymorphicInstance InstanceQ False tySch coercions []

      otherTypeConstraints <- enforceConstraints s constraints
      registerWantedTypeConstraints otherTypeConstraints

    -- Apply coercions
      ty <- substitute coercions' ty

      let elaborated = Val s ty rf (Constr ty c [])
          outputCtxt = usedGhostVariableContext
      return (ty, outputCtxt, [], elaborated)

    Nothing -> throw UnboundDataConstructor{ errLoc = s, errId = c }

-- Case synthesis
synthExpr defs gam pol (Case s _ rf guardExpr cases) = do
  debugM "synthExpr[Case]" (pretty s)
  -- Synthesise the type of the guardExpr
  (guardTy, guardGam, substG, elaboratedGuard) <- synthExpr defs gam pol guardExpr
  -- then synthesise the types of the branches

  -- Dependent / GADT pattern matches not allowed in a case
  ixed <- isIndexedType guardTy
  when ixed (throw $ CaseOnIndexedType s guardTy)

  -- (DEBUGGING) Determine if matching on type with more than one constructor
  isPolyShaped <- polyShaped guardTy

  -- if graded base
  scrutinee <-
    if usingExtension GradedBase
      then do
        s <- freshTyVarInContext (mkId "s") kcoeffect
        r <- freshTyVarInContext (mkId "scrutinee") (TyVar s)
        return (Just (TyVar r, TyVar s))
      else return Nothing


  newCaseFrame

  branchTysAndCtxtsAndSubsts <-
    forM cases $ \(pati, ei) -> do
      -- Build the binding context for the branch pattern
      newConjunct
      (patternGam, eVars, subst, elaborated_pat_i, _) <-
        ctxtFromTypedPattern' scrutinee s InCase guardTy pati NotFull
      newConjunct

      -- combine ghost variables from pattern using converge/meet
      innerGam <-
        if (SecurityLevels `elem` globalsExtensions ?globals)
        then ghostVariableContextMeet $ patternGam <> gam
        else return $ patternGam <> gam
      (tyCase, localGam, subst', elaborated_i) <- synthExpr defs innerGam pol ei

      -- Converge with the outer ghost variable
      patternGam' <-
        if (SecurityLevels `elem` globalsExtensions ?globals)
        then ghostVariableContextMeet $ (mkId ".var.ghost", fromJust $ lookup (mkId ".var.ghost") gam) : patternGam
        else return patternGam
      -- Check that the use of locally bound variables matches their bound type
      subst'' <- ctxtApprox s (localGam `intersectCtxts` patternGam) patternGam'

      -- Check linear use in this branch
      gamSoFar <- ctxtPlus s guardGam localGam
      case checkLinearity patternGam gamSoFar of
         -- Return the resulting computed context, without any of
         -- the variable bound in the pattern of this branch
         [] -> do
           substFinal <- combineManySubstitutions s [subst, subst', subst'']

           -- Conclude
           concludeImplication (getSpan pati) eVars

           return (tyCase
                    , (localGam `subtractCtxt` patternGam, substFinal)
                    , (elaborated_pat_i, elaborated_i))
         p:ps -> illLinearityMismatch s (p:|ps)

  let (branchTys, branchCtxtsAndSubsts, elaboratedCases) = unzip3 branchTysAndCtxtsAndSubsts
  let (branchCtxts, branchSubsts) = unzip branchCtxtsAndSubsts
  let branchTysAndSpans = zip branchTys (map (getSpan . snd) cases)

  -- All branches must be possible
  applySubstitutionsOnGuardPredicates s branchSubsts
  checkGuardsForImpossibility s (mkId "case") []

  popCaseFrame

  -- Finds the upper-bound return type between all branches
  (branchType, substBT) <-
         foldM (\(ty2, subst) (ty1, sp) -> do
                           jm <- joinTypesForEqualCoeffectGrades sp ty1 ty2
                           case jm of
                             Just (ty, subst', _) -> do
                               substF <- combineSubstitutions sp subst subst'
                               return (ty, substF)
                             Nothing ->
                                throw $ NoUpperBoundError{
                                  errLoc = sp
                                , errTy1 = ty1
                                , errTy2 = ty2
                                })
                   (head branchTys, [])
                   (tail branchTysAndSpans)

  -- Find the upper-bound type on the return contexts
  (branchesGam, tyVars) <- foldM (\(ctxt, vars) ctxt' -> do
    (ctxt'', vars') <- joinCtxts s ctxt ctxt'
    return (ctxt'', vars ++ vars')) (head branchCtxts, []) (tail branchCtxts)

  -- Contract the outgoing context of the guard and the branches (joined)
  (gamNew, gamNewSubst) <-
      if usingExtension GradedBase
      then do
        -- r * guardGam + branchesGam
        (guardGam', subst) <- ctxtMult s (fst $ fromJust scrutinee) guardGam
        ctxtPlus s branchesGam guardGam' <.*> (return subst)

      else ctxtPlus s branchesGam guardGam <.*> return []

  subst <- combineManySubstitutions s (substBT : substG : gamNewSubst : branchSubsts)

  -- Exisentially quantify any ty variables generated by joining contexts
  mapM_ (uncurry existentialTopLevel) tyVars

  let elaborated = Case s branchType rf elaboratedGuard elaboratedCases
  return (branchType, gamNew, subst, elaborated)

-- Diamond cut
-- let [[p]] <- [[e1 : sig]] in [[e2 : tau]]
synthExpr defs gam pol (LetDiamond s _ rf p optionalTySig e1 e2) = do
  debugM "synthExpr[LetDiamond]" (pretty s)
  (sig, gam1, subst1, elaborated1) <- synthExpr defs gam pol e1

  -- Check that a graded possibility type was inferred
  (ef1, ty1) <- case sig of
      Diamond ef1 ty1 -> return (ef1, ty1)
      t -> throw ExpectedEffectType{ errLoc = s, errTy = t }

  -- Type body of the let...
  -- ...in the context of the binders from the pattern
  (binders, _, substP, elaboratedP, _)  <- ctxtFromTypedPattern s InCase ty1 p NotFull
  pIrrefutable <- isIrrefutable s ty1 p
  unless pIrrefutable $ throw RefutablePatternError{ errLoc = s, errPat = p }
  (tau, gam2, subst2, elaborated2) <- synthExpr defs (binders <> gam) pol e2

  -- Check that a graded possibility type was inferred
  (ef2, ty2) <- case tau of
      Diamond ef2 ty2 -> return (ef2, ty2)
      t -> throw ExpectedEffectType{ errLoc = s, errTy = t }

  optionalSigEquality s optionalTySig ty1

  -- Check that usage matches the binding grades/linearity
  -- (performs the linearity check)
  subst0 <- ctxtApprox (getSpan e2) (gam2 `intersectCtxts` binders) binders

  gamNew <- ctxtPlus s (gam2 `subtractCtxt` binders) gam1

  debugM "ef1 =   ef2 = " (pretty ef1 ++ " - " ++ pretty ef2)
  (efTy, u) <- twoEqualEffectTypes s ef1 ef2
  -- Multiply the effects
  debugM "* efTy = " (pretty efTy)
  ef <- effectMult s efTy ef1 ef2
  let t = Diamond ef ty2

  subst <- combineManySubstitutions s [substP, subst0, subst1, subst2, u]
  -- Synth subst
  t' <- substitute substP t

  let elaborated = LetDiamond s t rf elaboratedP optionalTySig elaborated1 elaborated2
  return (t, gamNew, subst, elaborated)

-- Try catch
synthExpr defs gam pol (TryCatch s _ rf e1 p mty e2 e3) = do
  debugM "synthExpr[TryCatch]" (pretty s)

  (sig, gam1, subst1, elaborated1) <- synthExpr defs gam pol e1

  -- Check that a graded possibility type was inferred
  (ef1, opt, ty1) <- case sig of
    Diamond ef1 (Box opt ty1) ->
        return (ef1, opt, ty1)
    _ -> throw ExpectedOptionalEffectType{ errLoc = s, errTy = sig }

  (t, _, _) <- synthKind s opt
  addConstraint (ApproximatedBy s (TyGrade (Just t) 0) opt t)

  -- Type clauses in the context of the binders from the pattern
  (binders, _, substP, elaboratedP, _)  <- ctxtFromTypedPattern s InCase (Box opt ty1) (PBox s () False p) NotFull
  pIrrefutable <- isIrrefutable s ty1 p
  unless pIrrefutable $ throw RefutablePatternError{ errLoc = s, errPat = p }

  -- as branch
  (tau2, gam2, subst2, elaborated2) <- synthExpr defs (binders <> gam) pol e2

  -- catch branch
  (tau3, gam3, subst3, elaborated3) <- synthExpr defs gam pol e3

  -- check e2 and e3 are diamonds
  (ef2, ty2) <- case tau2 of
      Diamond ef2 ty2 -> return (ef2, ty2)
      t -> throw ExpectedEffectType{ errLoc = s, errTy = t }
  (ef3, ty3) <- case tau3 of
      Diamond ef3 ty3 -> return (ef3, ty3)
      t -> throw ExpectedEffectType{ errLoc = s, errTy = t }

  --to better match the typing rule both continuation types should be equal
  (b, ty, subst4) <- equalTypes s ty2 ty3
  b <- case b of
      True -> return b
      False -> throw TypeError{ errLoc = s, tyExpected = ty2, tyActual = ty3}

  optionalSigEquality s mty ty1

  -- linearity check for e2 and e3
  subst5 <- ctxtApprox s (gam2 `intersectCtxts` binders) binders

  -- compute output contexts
  (gam2u3, _) <- joinCtxts s (gam2 `subtractCtxt` binders) gam3
  gam'        <- ctxtPlus s gam1 gam2u3

  --resulting effect type
  let f = TyApp (TyCon $ mkId "Handled") ef1
  (efTy, subst') <- twoEqualEffectTypes s ef1 ef2
  g <- effectUpperBound s efTy ef2 ef3
  ef <- effectMult s efTy f g
  let t = Diamond ef ty

  subst <- combineManySubstitutions s [substP, subst1, subst2, subst3, subst4, subst5, subst']
  -- Synth subst
  t' <- substitute substP t

  let elaborated = TryCatch s t rf elaborated1 elaboratedP mty elaborated2 elaborated3
  return (t, gam', subst, elaborated)

-- Variables
synthExpr defs gam _ (Val s _ rf (Var _ x)) = do
   debugM "synthExpr[Var]" (pretty s)

   -- Try the local context
   case lookup x gam of
     Nothing ->
       -- Try definitions in scope
       case lookup x (defs <> Primitives.builtins) of
         Just tyScheme  -> do
           (ty, ctxt, subst, elab) <- freshenTySchemeForVar s rf x tyScheme
           -- Mark ghost variable as used.
           return (ty, unprotectedGhostVariableContext <> ctxt, subst, elab)

         -- Couldn't find it
         Nothing -> throw UnboundVariableError{ errLoc = s, errId = x }

     -- In the local context
     Just (Linear ty)       -> do
       let elaborated = Val s ty rf (Var ty x)
       return (ty, usedGhostVariableContext <> [(x, Linear ty)], [], elaborated)

     Just (Discharged ty c) -> do
       (k, subst, _) <- synthKind s c
       let elaborated = Val s ty rf (Var ty x)
       return (ty, usedGhostVariableContext <> [(x, Discharged ty (TyGrade (Just k) 1))], subst, elaborated)

     -- cannot use a Ghost variable explicitly
     Just (Ghost c) -> throw UnboundVariableError{ errLoc = s, errId = x }

-- Capabilities
-- matches a pattern: `cap CapName carrier`
synthExpr defs gam pol
      (App s _ rf
        (App _ _ _
           (Val _ _ _ (Var _ (internalName -> "cap")))
           (Val _ _ _ (Constr _ capName _)))
        carrier) = do

  -- Do we have this capabillity?
  case lookup capName Primitives.capabilities of
    Nothing -> throw UnboundVariableError{ errLoc = s, errId = capName }
    Just ty -> do
      -- Type the capability as a box thing
      (outContext, subst, _) <- checkExpr defs gam pol False (Box (TySet Normal [TyCon capName]) (TyCon $ mkId "()")) carrier

      -- elaborate just to a variable application
      let elab = Val s ty rf (Var ty (mkId $ "cap." <> internalName capName))
      return (ty, outContext, subst, elab)

-- Specialised application for scale
{- TODO: needs thought -}
synthExpr defs gam pol
      (App s _ rf (Val s' _ rf' (Var _ v)) (Val s'' _ rf'' (NumFloat r))) | internalName v == "scale" = do
  debugM "synthExpr[scale]" (pretty s)

  let floatTy = TyCon $ mkId "DFloat"

  let scaleTyApplied = FunTy Nothing Nothing (Box (TyRational (toRational r)) floatTy) floatTy
  let scaleTy = FunTy Nothing Nothing floatTy scaleTyApplied

  let elab = App s scaleTy rf (Val s' scaleTy rf' (Var scaleTy v)) (Val s'' floatTy rf'' (NumFloat r))

  return (scaleTyApplied, weakenedGhostVariableContext, [], elab)

-- Application
synthExpr defs gam pol (App s _ rf e e') | not (usingExtension GradedBase) = do
    debugM "synthExpr[App]" (pretty s)
    (fTy, gam1, subst1, elaboratedL) <- synthExpr defs gam pol e

    case fTy of
      -- Got a function type for the left-hand side of application
      (FunTy _ _ sig tau) -> do
         (gam2, subst2, elaboratedR) <- checkExpr defs gam (flipPol pol) False sig e'
         gamNew <- ctxtPlus s gam1 gam2

         subst <- combineSubstitutions s subst1 subst2

         -- Synth subst
         tau    <- substitute subst tau

         let elaborated = App s tau rf elaboratedL elaboratedR
         return (tau, gamNew, subst, elaborated)

         -- Not a function type
      t -> throw LhsOfApplicationNotAFunction{ errLoc = s, errTy = fTy }

-- Application
-- GRADED BASE

synthExpr defs gam pol (App s _ rf e1 e2) | usingExtension GradedBase = do
  debugM "synthExpr[App-graded-base]" (pretty s)

--
--      G1 |- e1 => a %r -> b    G2 |- e2 <= a
--  -------------------------------------------- app
--      G1 + r * G2 |- e1 e2 => b
--
  -- Syntheise type of function
  (funTy, gam1, subst1, elab_e1) <- synthExpr defs gam pol e1
  case funTy of
    FunTy _ grade sig tau -> do
      -- Check whether `e2` can be promoted (implicitly by this rule)
      unpr <-
        if (CBN `elem` globalsExtensions ?globals)
        then return False
        else return $ resourceAllocator e2
      when unpr (throw $ UnpromotableError{errLoc = s, errTy = sig })

      -- Check the argument against `sig`
      (gam2, subst2, elab_e2) <- checkExpr defs gam pol False sig e2

      let r = case grade of
                Just r  -> r
                -- No grade so implicitly 1 of any semiring
                Nothing -> TyGrade Nothing 1

      -- Multiply the context
      (scaled_gam2, subst2') <- ctxtMult s r gam2
      gam_out <- ctxtPlus s gam1 scaled_gam2

      -- Output
      substFinal <- combineManySubstitutions s [subst1, subst2, subst2']
      let elaborated = App s tau rf elab_e1 elab_e2
      return (tau, gam_out, substFinal, elaborated)

    _ -> throw LhsOfApplicationNotAFunction{ errLoc = s, errTy = funTy }

{- Promotion

[G] |- e : t
 ---------------------
[G]*r |- [e] : []_r t

-}

synthExpr defs gam pol (Val s _ rf (Promote _ e)) = do
   debugM "synthExpr[Prom]" (pretty s)

   -- Create a fresh kind variable for this coeffect
   vark <- freshIdentifierBase $ "kprom_[" <> pretty (startPos s) <> "]"
   -- remember this new kind variable in the kind environment
   modify (\st -> st { tyVarContext = (mkId vark, (kcoeffect, InstanceQ)) : tyVarContext st })

   -- Create a fresh coeffect variable for the coeffect of the promoted expression
   var <- freshTyVarInContext (mkId $ "prom_[" <> pretty (startPos s) <> "]") (tyVar vark)

   -- Synth type of promoted expression
   (t, gam', subst, elaboratedE) <- synthExpr defs gam pol e

   promotable <-
      if (CBN `elem` globalsExtensions ?globals)
        then return True
        -- In CBV mode, check we do not have a resource allocator here
        else return $ (not (resourceAllocator e)
        -- or see if we have turned on unsafe promotion
                   || (UnsafePromotion `elem` globalsExtensions ?globals))
   when (not promotable) (throw $ UnpromotableError{errLoc = s, errTy = t})

   -- Multiply the grades of all the used variables here
   (gam'', subst') <- ctxtMult s (TyVar var) gam'

   substFinal <- combineManySubstitutions s [subst, subst']
   let finalTy = Box (TyVar var) t

   let elaborated = Val s finalTy rf (Promote t elaboratedE)
   return (finalTy, gam'', substFinal, elaborated)

{- Necessitation

. |- e : T
-----------
[G] |- *e : *T

-}

synthExpr defs gam pol (Val s _ rf (Nec _ e)) = do
  debugM "synthExpr[Nec]" (pretty s)

   -- Create a fresh kind variable for this guarantee
  vark <- freshIdentifierBase $ "knec_[" <> pretty (startPos s) <> "]"
   -- remember this new kind variable in the kind environment
  modify (\st -> st { tyVarContext = (mkId vark, (kguarantee, InstanceQ)) : tyVarContext st })

   -- Create a fresh guarantee variable for the guarantee of the necessitated expression
  var <- freshTyVarInContext (mkId $ "nec_[" <> pretty (startPos s) <> "]") (tyVar vark)

  -- Synth type of necessitated expression
  (t, gam', subst, elaboratedE) <- synthExpr defs gam pol e

  let finalTy = Star (TyVar var) t
  let elaborated = Val s finalTy rf (Nec t elaboratedE)
  return (finalTy, gam', subst, elaborated)

-- BinOp
synthExpr defs gam pol (Binop s _ rf op e1 e2) = do
    debugM "synthExpr[BinOp]" (pretty s)

    {-

      synthExpr here involves trying to do some resolution due to overload
      The generalise idea is:
        * First we synth the types of both subterms (e1 and e2) and see if this operator
          is defined at that type
        * If this fails, we can see if checking e2 against the synthed type of e1 works, and
          then yields an operator we have at those types
        * Otherwise we try the symmetric case of checking e1 against the synted type of e2,
          and then seeing if we have an oeprator at that type
        * Otherwise we cannot resolve

    -}

    (t1, gam1, subst1, elaboratedL) <- synthExpr defs gam pol e1
    (t2, gam2, subst2, elaboratedR) <- synthExpr defs gam pol e2
    -- Look through the list of operators (of which there might be
    -- multiple matching operators)
    let operatorTypes = NonEmpty.toList . Primitives.binaryOperators $ op
    mReturnType <- selectFirstByType t1 t2 operatorTypes

    (returnType, gam1, gam2, subst1, subst2, elaborateL, elaborateR) <-
      case mReturnType of
        Just returnType -> return (returnType, gam1, gam2, subst1, subst2, elaboratedL, elaboratedR)
        -- Nothing matched so...
        Nothing -> do
          -- ...alternatively see if we can check `e2` against the type of `e1`
          -- This must be done inside a 'peekChecker' block as it might fail
          (result, local) <- peekChecker $ do
                (gam2, subst2, elaboratedR) <- checkExpr defs gam pol False t1 e2
                mReturnType <- selectFirstByType t1 t1 operatorTypes
                -- If its Nothing then thrown any error, otherwise return the type
                maybe (throw undefined) return mReturnType

          case result of
            Right returnType -> local >> return (returnType, gam1, gam2, subst1, subst2, elaboratedL, elaboratedR)
            -- Didn't match so see if we can resolve things symmetricall, checking `e1` against the type of `e2`
            Left _ -> do
              (result, local) <- peekChecker $ do
                (gam1, subst1, elaboratedL) <- checkExpr defs gam pol False t2 e1
                mReturnType <- selectFirstByType t2 t2 operatorTypes
                -- If its Nothing then thow any error, otherwise return the type
                maybe (throw undefined) return mReturnType

              case result of
                Right returnType -> local >> return (returnType, gam1, gam2, subst1, subst2, elaboratedL, elaboratedR)
                -- Seems no way to resolve this:
                Left _ ->
                  throw FailedOperatorResolution { errLoc = s, errOp = op, errTy = t1 .-> t2 .-> tyVar "?" }

    gamOut <- ctxtPlus s gam1 gam2
    subst <- combineSubstitutions s subst1 subst2
    let elaborated = Binop s returnType rf op elaboratedL elaboratedR
    return (returnType, gamOut, subst, elaborated)

  where
    -- No matching type were found (meaning there is a type error)
    selectFirstByType t1 t2 [] = return Nothing

    selectFirstByType t1 t2 ((FunTy _ grade1 opt1 (FunTy _ grade2 opt2 resultTy)):ops) = do
      -- Attempt to use this typing
      (result, local) <- peekChecker $ do
         (eq1, substA, _) <- equalTypes s t1 opt1
         (eq2, substB, _) <- equalTypes s t2 opt2
         -- TODO: note substitutions getting discared here
         return (eq1 && eq2)
      -- If successful then return this local computation
      case result of
        Right True -> local >> return (Just resultTy)
        _          -> selectFirstByType t1 t2 ops

    selectFirstByType t1 t2 (_:ops) = selectFirstByType t1 t2 ops


-- Abstraction, can only synthesise the types of
-- lambda in Church style (explicit type)
synthExpr defs gam pol (Val s _ rf (Abs _ p (Just sig) e)) = do
  debugM "synthExpr[Abs[church]]" (pretty s)

  newConjunct

  (bindings, localVars, substP, elaboratedP, _) <- ctxtFromTypedPattern s InCase sig p NotFull

  newConjunct

  pIrrefutable <- isIrrefutable s sig p
  if pIrrefutable then do
     (tau, gam'', subst, elaboratedE) <- synthExpr defs (bindings <> gam) pol e

     -- Locally we should have this property (as we are under a binder)
     subst0 <- ctxtApprox s (gam'' `intersectCtxts` bindings) bindings

     let finalTy = FunTy Nothing Nothing sig tau
     let elaborated = Val s finalTy rf (Abs finalTy elaboratedP (Just sig) elaboratedE)

     substFinal <- combineManySubstitutions s [subst0, substP, subst]
     finalTy' <- substitute substP finalTy

     concludeImplication s localVars

     return (finalTy', gam'' `subtractCtxt` bindings, substFinal, elaborated)

  else throw RefutablePatternError{ errLoc = s, errPat = p }

-- Abstraction, can only synthesise the types of
-- lambda in Curry style (no type)
synthExpr defs gam pol (Val s _ rf (Abs _ p Nothing e)) = do
  debugM "synthExpr[Abs[curry]]" (pretty s)

  newConjunct

  -- if graded base
  scrutinee <-
    if usingExtension GradedBase
      then do
        s <- freshTyVarInContext (mkId "s") kcoeffect
        r <- freshTyVarInContext (mkId "scrutinee") (TyVar s)
        return (Just (TyVar r, TyVar s))
      else
        return Nothing

  tyVar <- freshTyVarInContext (mkId "t") (Type 0)
  let sig = (TyVar tyVar)

  (bindings, localVars, substP, elaboratedP, _) <- ctxtFromTypedPattern' scrutinee s InCase sig p NotFull

  newConjunct

  pIrrefutable <- isIrrefutable s sig p
  if pIrrefutable then do
     (tau, gam'', subst, elaboratedE) <- synthExpr defs (bindings <> gam) pol e

     -- Locally we should have this property (as we are under a binder)
     debugM "abs-inner-check:" (pretty (gam'' `intersectCtxts` bindings) <> "<: " <> pretty bindings)
     subst0 <- ctxtApprox s (gam'' `intersectCtxts` bindings) bindings

     let finalTy = FunTy Nothing (fmap fst scrutinee) sig tau
     let elaborated = Val s finalTy rf (Abs finalTy elaboratedP (Just sig) elaboratedE)
     finalTy' <- substitute substP finalTy
     substFinal <- combineManySubstitutions s [subst0, substP, subst]

     concludeImplication s localVars

     return (finalTy', gam'' `subtractCtxt` bindings, substFinal, elaborated)
  else throw RefutablePatternError{ errLoc = s, errPat = p }

-- Explicit type application
synthExpr defs gam pol e@(AppTy s _ rf e1 ty) = do
  debugM "synthExpr[AppTy]" (pretty s)
  -- Check to see if this type application is an instance of a deriving construct
  case e1 of
    (Val _ _ _ (Var _ (internalName -> "push"))) -> do
      st <- get
      let name = mkId $ "push@" ++ pretty ty
      case lookup (mkId "push", ty) (derivedDefinitions st) of
        Just (tyScheme, _) ->
          freshenTySchemeForVar s rf name tyScheme

        Nothing -> do
          -- Get this derived
          (typScheme, def) <- derivePush s ty
          debugM "derived push:" (pretty def)
          debugM "derived push tys:" (show typScheme)

          -- Register the definition that has been derived
          modify (\st -> st { derivedDefinitions = ((mkId "push", ty), (typScheme, def)) : derivedDefinitions st })

          -- return this variable expression in place here
          freshenTySchemeForVar s rf name typScheme

    (Val _ _ _ (Var _ (internalName -> "pull"))) -> do
      st <- get
      let name = mkId $ "pull@" ++ pretty ty
      case lookup (mkId "pull", ty) (derivedDefinitions st) of
        Just (tyScheme, _) ->
          freshenTySchemeForVar s rf name tyScheme

        Nothing -> do
          -- Get this derived
          (typScheme, def) <- derivePull s ty
          -- Register the definition that has been derived
          modify (\st -> st { derivedDefinitions = ((mkId "pull", ty), (typScheme, def)) : derivedDefinitions st })
          -- return this variable expression in place here
          freshenTySchemeForVar s rf name typScheme
    (Val _ _ _ (Var _ (internalName -> "copyShape"))) -> do
      st <- get
      let name = mkId $ "copyShape@" ++ pretty ty
      case lookup (mkId "copyShape", ty) (derivedDefinitions st) of
        Just (tyScheme, _) ->
          freshenTySchemeForVar s rf name tyScheme
        Nothing -> do
          -- Get this derived
          (typScheme, mdef) <- deriveCopyShape s ty
          -- Register the definition that has been derived
          case mdef of
            Nothing  -> return ()
            Just def -> do
              debugM "derived copyShape:" (pretty def)
              modify (\st -> st { derivedDefinitions = ((mkId "copyShape", ty), (typScheme, def)) : derivedDefinitions st })

          debugM "derived copyShape tys:" (show typScheme)
          -- return this variable expression in place here
          freshenTySchemeForVar s rf name typScheme

    (Val _ _ _ (Var _ (internalName -> "drop"))) -> do
      st <- get
      let name = mkId $ "drop@" ++ pretty ty
      case lookup (mkId "drop", ty) (derivedDefinitions st) of
        Just (tyScheme, _) ->
          freshenTySchemeForVar s rf name tyScheme
        Nothing -> do
          -- Get this derived
          (typScheme, mdef) <- deriveDrop s ty
          -- Register the definition that has been derived
          case mdef of
            Nothing  -> return ()
            Just def -> do
              debugM "derived drop:" (pretty def)
              modify (\st -> st { derivedDefinitions = ((mkId "drop", ty), (typScheme, def)) : derivedDefinitions st })

          debugM "derived drop tys:" (pretty typScheme)
          -- return this variable expression in place here
          freshenTySchemeForVar s rf name typScheme

    expr -> do
      -- Synth expr, expecting it to be a forall now
      (retTy, gam', subst, elab) <- synthExpr defs gam pol expr
      case retTy of
        (TyForall var kind receiverTy) -> do
          tyA   <- substitute [(var, SubstT ty)] receiverTy
          elab' <- substitute [(var, SubstT ty)] elab
          return (tyA, gam', subst, elab')

        _ ->
          throw LhsOfTyApplicationNotForall{ errLoc = getSpan e, errTy = retTy }

--  G |- e : ty'[ty/x]
-- ------------------------------------------------
--  G |- pack < ty , e > as exists {x : k} . ty' : exists {x : k} . ty'
synthExpr defs gam pol (Val s0 _ rf p@(Pack sp a ty e x k ty')) = do
  debugM "synthExpr[pack]" (pretty p)
  innerType <- substitute [(x, SubstT ty)] ty'
  (gam, subst, elabE) <- checkExpr defs gam pol False innerType e
  let retTy = TyExists x k ty'
  let elab = Val s0 retTy rf (Pack sp retTy ty elabE x k ty')
  return (retTy, gam, subst, elab)


-- G |- e : A
-- ------------------------------------------
-- G |- /\(x : t) . e : forall {x : t} . A

synthExpr defs gam pol (Val s0 _ rf val@(TyAbs a (Left (v, k)) e)) = do
  debugM "synthExpr [forall]" (pretty val)
  registerTyVarInContextWith' v k ForallQ $ do
    (ty, gam, subst, elabE) <- synthExpr defs gam pol e
    let retTy = TyForall v k ty
    let elab = Val s0 retTy rf (TyAbs retTy (Left (v, k)) elabE)
    return (TyForall v k ty, gam, subst, elab)

-- Implicit lifting of type scheme to rankN
--- G |- var : forall {id : k} . A
--- -------------------------------------
-- G |- /\{id} . var : (forall {id : t} . A)

synthExpr defs gam pol (Val s _ rf val@(TyAbs a (Right ids) e)) = do
    case e of
      Val _ _ _ (Var _ x) ->
        case lookup x (defs <> Primitives.builtins) of
          Just tyScheme@(Forall s0 bindings constraints tyInner)  -> do
            let (tyRankN, bindings') = build ids bindings tyInner
            let newTyScheme = Forall s0 bindings' constraints tyRankN
            (ty', ctxt, subst, elab) <- freshenTySchemeForVar s rf x newTyScheme
            return (ty', ctxt, subst, elab)

          Nothing -> throw UnboundVariableError{ errLoc = s, errId = x }
      _ ->
        error "Can only do implicit lifting of type scheme to rankN types on a variable"


  where
    build [] bindings tyInner = (tyInner, bindings)
    build (var:vars) bindings tyInner =
      case lookupAndCutoutBy sourceName var bindings of
        Nothing -> build vars bindings tyInner
        Just (rest, (var', ty))  ->
            let (tyInner', bindings') = build vars rest tyInner
            in (TyForall var' ty tyInner', bindings')


--
-- G |- e1 : exists {y : k} . A
-- G, forall tyx : k,  x : A[tyx/y] |- e2 : B
-- tyx notin fvB(B)
-- -----------------------------------------
-- G |- unpack < tyx , x > = e1 in e2 : B
synthExpr defs gam pol e@(Unpack s a rf tyVar var e1 e2) = do
  debugM "synthExpr[unpack]" (pretty e)
  (ty, gam1, subst1, elabE1) <- synthExpr defs gam pol e1
  case ty of
    TyExists y k tyA -> do
      -- line up the types
      tyA <- substitute [(y, SubstT $ TyVar tyVar)] tyA
      let bindings = [(var, Linear tyA)]
      let gam' = bindings ++ gam
      registerTyVarInContext tyVar k ForallQ
      (tyB, gam2, subst2, elabE2)  <- synthExpr defs gam' pol e2
      -- Check that the existential var doesn't escape
      if not (tyVar `elem` freeVars tyB)
        then do
          case checkLinearity bindings gam' of
            [] -> do
              gamOut <- ctxtPlus s gam1 gam2
              substFinal <- combineManySubstitutions s [subst1, subst2]

              let elab = Unpack s tyB rf tyVar var elabE1 elabE2
              return (tyB, gamOut `subtractCtxt` [(var, Linear tyA)], substFinal, elab)

            (p:ps) -> illLinearityMismatch s (p:|ps)

        else throw EscapingExisentialVar{ errLoc = s, var = tyVar, errTy = tyB }


    _ -> throw LhsOfUnpackNotAnExistential{ errLoc = s, errTy = ty }


synthExpr _ _ _ e = do
  debugM "synthExpr[*]" (pretty (getSpan e))
  throw NeedTypeSignature{ errLoc = getSpan e, errExpr = e }

-- Check an optional type signature for equality against a type
optionalSigEquality :: (?globals :: Globals) => Span -> Maybe Type -> Type -> Checker ()
optionalSigEquality _ Nothing _ = pure ()
optionalSigEquality s (Just t) t' = do
  _ <- equalTypes s t' t
  pure ()

solveConstraints :: (?globals :: Globals) => Pred -> Span -> Id -> Checker ()
solveConstraints predicate s name = do

  -- Get the coeffect kind context and constraints
  checkerState <- get
  let ctxtCk  = tyVarContext checkerState
  coeffectVars <- includeOnlyGradeVariables s ctxtCk
  -- remove any variables bound already in the predicate
  coeffectVars <- return (coeffectVars `deleteVars` boundVars predicate)

  debugM "tyVarContext" (pretty $ tyVarContext checkerState)
  debugM "context into the solver" (pretty $ coeffectVars)
  debugM "Solver predicate" $ pretty predicate -- <> "\n" <> show predicate

  constructors <- allDataConstructorNames
  (_, result) <- liftIO $ provePredicate predicate coeffectVars constructors
  case result of
    QED -> do
      debugM "Solver result" "QED."
      return ()
    NotValid msg -> do
      debugM "Solver result" ("False: " <> msg)

      msg' <- rewriteMessage msg
      simplPred <- simplifyPred predicate

      -- try trivial unsats again
      let unsats' = trivialUnsatisfiableConstraints simplPred
      if not (null unsats')
        then mapM_ (\c -> throw GradingError{ errLoc = getSpan c, errConstraint = Neg c }) unsats'
        else
          if msg' == "is Falsifiable\n"
            then throw SolverErrorFalsifiableTheorem
              { errLoc = s, errDefId = name, errPred = simplPred }
            else throw SolverErrorCounterExample
              { errLoc = s, errDefId = name, errPred = simplPred, message = prettifyMessage msg' }
      where

    NotValidTrivial unsats ->
       mapM_ (\c -> throw GradingError{ errLoc = getSpan c, errConstraint = Neg c }) unsats
    Timeout -> do
        debugM "Solver result" "Timeout"
        throw SolverTimeout{ errLoc = s, errSolverTimeoutMillis = solverTimeoutMillis, errDefId = name, errContext = "grading", errPred = predicate }
    OtherSolverError msg -> do
      debugM "Solver result" ("Other error: " <> msg)
      simplPred <- simplifyPred predicate
      msg' <- rewriteMessage msg
      throw SolverError{ errLoc = s, errMsg = msg', errPred = simplPred }
    SolverProofError msg -> error msg

-- Rewrite an error message coming from the solver
rewriteMessage :: (?globals :: Globals) => String -> Checker String
rewriteMessage msg = do
    st <- get
    let tyVars = tyVarContext st
    let msgLines = T.lines $ T.pack msg
    -- Rewrite internal names to source names
    let msgLines' = map (\line -> foldl convertLine line tyVars) msgLines

    return $ T.unpack (T.unlines msgLines')
  where
    convertLine line (v, (k, _)) =
        -- Try to replace line variables in the line
       let line' = T.replace (T.pack (internalName v)) (T.pack (sourceName v)) line
       -- If this succeeds we might want to do some other replacements
           line'' =
             if line /= line' then
               case k of
                 (TyCon (internalName -> "Level")) ->
                    T.replace (T.pack $ show privateRepresentation) (T.pack "Private")
                      (T.replace (T.pack $ show publicRepresentation) (T.pack "Public")
                          (T.replace (T.pack "Integer") (T.pack "Level") line'))
                 (TyVar _ ) -> T.replace (T.pack "Integer") (T.pack $ pretty k) line'
                 _ -> line'
             else line'
       in line''

prettifyMessage :: String -> String
prettifyMessage msg =
  if falso `isPrefixOf` msg
    then drop (length falso + 1) msg
    else msg
  where falso = "is Falsifiable."

-- | `ctxtEquals ctxt1 ctxt2` checks if two contexts are equal
--   and the typical pattern is that `ctxt2` represents a specification
--   (i.e. input to checking) and `ctxt1` represents actually usage
ctxtApprox :: (?globals :: Globals) =>
    Span -> Ctxt Assumption -> Ctxt Assumption -> Checker Substitution
ctxtApprox s ctxt1 ctxt2 = do
  -- intersection contains those ids (and substitutions) from ctxt1 which appears in ctxt2
  intersection <-
    -- For everything in the right context
    -- (which should come as an input to checking)
    forM ctxt2 $ \(id, ass2) ->
      -- See if it appears in the left context...
      case lookup id ctxt1 of
        -- ... if so equate
        Just ass1 -> do
          subst <- relateByAssumption s ApproximatedBy (id, ass1) (id, ass2)
          return (id, subst)
        -- ... if not check to see if the missing variable is linear
        Nothing   ->
           case ass2 of
             -- Linear gets instantly reported
             Linear t -> illLinearityMismatch s . pure $ LinearNotUsed id
             -- Else, this could be due to weakening so see if this is allowed
             Discharged t c -> do
               -- TODO: deal with the subst here
               (kind, subst, _) <- synthKind s c
               -- TODO: deal with the subst here
               subst' <- relateByAssumption s ApproximatedBy (id, Discharged t (TyGrade (Just kind) 0)) (id, ass2)
               subst'' <- combineSubstitutions s subst subst'
               return (id, subst'')
             -- TODO: handle new ghost variables
             Ghost c -> do
               -- TODO: deal with the subst here
               (kind, subst, _) <- synthKind s c
               debugM "ctxtApprox ghost" (pretty kind <> ", " <> pretty c)
               -- TODO: deal with the subst here
               subst' <- relateByAssumption s ApproximatedBy (id, Ghost (TyGrade (Just kind) 0)) (id, ass2)
               subst'' <- combineSubstitutions s subst subst'
               return (id, subst'')
  -- Last we sanity check, if there is anything in ctxt1 that is not in ctxt2
  -- then we have an issue!
  let justIds = map fst intersection
  forM_ ctxt1 $ \(id, ass1) ->
    if (id `elem` justIds)
      then return ()
      else throw UnboundVariableError{ errLoc = s, errId = id }

  -- combine and return substitutions
  combineManySubstitutions s (map snd intersection)

-- | `ctxtEquals ctxt1 ctxt2` checks if two contexts are equal
--   and the typical pattern is that `ctxt2` represents a specification
--   (i.e. input to checking) and `ctxt1` represents actually usage
ctxtEquals :: (?globals :: Globals) =>
    Span -> Ctxt Assumption -> Ctxt Assumption -> Checker Substitution
ctxtEquals s ctxt1 ctxt2 = do
  -- intersection contains those ids from ctxt1 which appears in ctxt2
  intersection <-
    -- For everything in the right context
    -- (which should come as an input to checking)
    forM ctxt2 $ \(id, ass2) ->
      -- See if it appears in the left context...
      case lookup id ctxt1 of
        -- ... if so equate
        Just ass1 -> do
          -- -- TODO: deal with the subst here
          subst <- relateByAssumption s Eq (id, ass1) (id, ass2)
          return (id, subst)
        -- ... if not check to see if the missing variable is linear
        Nothing   ->
           case ass2 of
             -- Linear gets instantly reported
             Linear t -> illLinearityMismatch s . pure $ LinearNotUsed id
             -- Else, this could be due to weakening so see if this is allowed
             Discharged t c -> do
               (kind, subst, _) <- synthKind s c
               subst' <- relateByAssumption s Eq (id, Discharged t (TyGrade (Just kind) 0)) (id, ass2)
               subst'' <- combineSubstitutions s subst subst'
               return (id, subst'')
             -- TODO: handle new ghost variables
             Ghost c -> do
               -- TODO: deal with the subst here
               (kind, subst, _) <- synthKind s c
               -- TODO: deal with the subst here
               subst' <- relateByAssumption s Eq (id, Ghost (TyGrade (Just kind) 0)) (id, ass2)
               subst'' <- combineSubstitutions s subst subst'
               return (id, subst'')
  -- Last we sanity check, if there is anything in ctxt1 that is not in ctxt2
  -- then we have an issue!
  let justIds = map fst intersection
  forM_ ctxt1 $ \(id, ass1) ->
    if (id `elem` justIds)
      then return ()
      else throw UnboundVariableError{ errLoc = s, errId = id }

  -- return substitutions
  combineManySubstitutions s (map snd intersection)

{- | Take the least-upper bound of two contexts.
     If one context contains a linear variable that is not present in
    the other, then the resulting context will not have this linear variable.
    Also return s a list of new type variable created to do the join. -}
joinCtxts :: (?globals :: Globals) => Span -> Ctxt Assumption -> Ctxt Assumption
  -> Checker (Ctxt Assumption, Ctxt Kind)
joinCtxts s ctxt1 ctxt2 = do
    -- All the type assumptions from ctxt1 whose variables appear in ctxt2
    -- and weaken all others
    ctxt  <- intersectCtxtsWithWeaken s ctxt1 ctxt2
    -- All the type assumptions from ctxt2 whose variables appear in ctxt1
    -- and weaken all others
    ctxt' <- intersectCtxtsWithWeaken s ctxt2 ctxt1

    -- Make an context with fresh coeffect variables for all
    -- the variables which are in both ctxt1 and ctxt2...
    (varCtxt, tyVars) <- freshVarsIn s (map fst ctxt) ctxt
    (_, tyVars') <- freshVarsIn s (map fst ctxt') ctxt'
    tyVars'' <- zip (map fst tyVars) <$> zipWithM generalise (map snd tyVars) (map snd tyVars')

    -- ... and make these fresh coeffects the upper-bound of the coeffects
    -- in ctxt and ctxt'
    _ <- zipWith3M_ (relateByLUB s) ctxt ctxt' varCtxt
    -- Return the common upper-bound context of ctxt1 and ctxt2
    return (varCtxt, tyVars'')
  where
    generalise t1 t2 = fst3 <$> mguCoeffectTypes s t1 t2

    zipWith3M_ :: Monad m => (a -> b -> c -> m d) -> [a] -> [b] -> [c] -> m [d]
    zipWith3M_ f _ _ [] = return []
    zipWith3M_ f _ [] _ = return []
    zipWith3M_ f [] _ _ = return []
    zipWith3M_ f (x:xs) (y:ys) (z:zs) = do
      w <- f x y z
      ws <- zipWith3M_ f xs ys zs
      return $ w : ws

{- |  intersect contexts and weaken anything not appear in both
        relative to the left context (this is not commutative) -}
intersectCtxtsWithWeaken
  :: (?globals :: Globals)
  => Span
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Checker (Ctxt Assumption)
intersectCtxtsWithWeaken s a b = do
   let intersected = intersectCtxts a b
   -- All the things that were not shared
   let remaining   = b `subtractCtxt` intersected
   let leftRemaining = a `subtractCtxt` intersected

   let linearNotUsedInBoth =
         flip mapMaybe (leftRemaining <> remaining) (\(v, ass) ->
           case ass of
             Linear t -> Just $ LinearNotUsed v
             _        -> Nothing)

   case linearNotUsedInBoth of
     -- All linear things used equally
     [] -> do
        weakenedRemaining <- mapM weaken remaining
        let newCtxt = intersected <> filter isNonLinearAssumption (weakenedRemaining <> leftRemaining)
        return . normaliseCtxt $ newCtxt

     (p:ps) -> illLinearityMismatch s (p:|ps)

  where
   isNonLinearAssumption :: (Id, Assumption) -> Bool
   isNonLinearAssumption (_, Discharged _ _) = True
   isNonLinearAssumption (_, Ghost _)        = True
   isNonLinearAssumption _                   = False

   weaken :: (Id, Assumption) -> Checker (Id, Assumption)
   weaken (var, Linear t) =
       return (var, Linear t)
   weaken (var, Discharged t c) = do
        -- TODO: deal with the subst here
       (kind, _, _) <- synthKind s c
       return (var, Discharged t (TyGrade (Just kind) 0))
   weaken (var, Ghost c) = do
       -- TODO: handle new ghost variables
       -- TODO: do we want to weaken ghost variables?
       (kind, _, _) <- synthKind s c
       debugM "weaken ghost" (pretty kind <> ", " <> pretty c)
       return (var, Ghost (TyGrade (Just kind) 0))

{- | Given an input context and output context, check the usage of
     variables in the output, returning a list of usage mismatch
     information if, e.g., a variable is bound linearly in the input but is not
     used in the output, or is discharged in the output -}
checkLinearity :: Ctxt Assumption -> Ctxt Assumption -> [LinearityMismatch]
checkLinearity [] _ = []
checkLinearity ((v, Linear _):inCtxt) outCtxt =
  case lookup v outCtxt of
    -- Good: linear variable was used
    Just Linear{} -> checkLinearity inCtxt outCtxt
    -- Bad: linear variable was discharged (boxed var but binder not unboxed)
    Just Discharged{} -> LinearUsedNonLinearly v : checkLinearity inCtxt outCtxt
    -- TODO: handle new ghost variables
    Just Ghost{} -> LinearUsedNonLinearly v : checkLinearity inCtxt outCtxt
    Nothing -> LinearNotUsed v : checkLinearity inCtxt outCtxt

checkLinearity ((_, Discharged{}):inCtxt) outCtxt =
  -- Discharged things can be discarded, so it doesn't matter what
  -- happens with them
  checkLinearity inCtxt outCtxt
-- TODO: handle new ghost variables
checkLinearity ((_, Ghost{}):inCtxt) outCtxt =
  -- Discharged things can be discarded, so it doesn't matter what
  -- happens with them
  checkLinearity inCtxt outCtxt

-- Assumption that the two assumps are for the same variable
relateByAssumption :: (?globals :: Globals)
  => Span
  -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
  -> (Id, Assumption)
  -> (Id, Assumption)
  -> Checker Substitution

-- Linear assumptions ignored
relateByAssumption _ _ (_, Linear _) (_, Linear _) = return []

-- Discharged coeffect assumptions
relateByAssumption s rel (_, Discharged _ c1) (_, Discharged _ c2) = do
  (kind, subst, (inj1, inj2)) <- mguCoeffectTypesFromCoeffects s c1 c2
  addConstraint (rel s (inj1 c1) (inj2 c2) kind)
  return subst

-- TODO: handle new ghost variables
relateByAssumption s rel (_, Ghost c1) (_, Ghost c2) = do
  (kind, subst, (inj1, inj2)) <- mguCoeffectTypesFromCoeffects s c1 c2
  addConstraint (rel s (inj1 c1) (inj2 c2) kind)
  return subst

relateByAssumption s rel (_, Discharged _ c1) (_, Ghost c2) = do
  (kind, subst, (inj1, inj2)) <- mguCoeffectTypesFromCoeffects s c1 c2
  addConstraint (rel s (inj1 c1) (inj2 c2) kind)
  return subst

relateByAssumption s rel (_, Ghost c1) (_, Discharged _ c2) = do
  (kind, subst, (inj1, inj2)) <- mguCoeffectTypesFromCoeffects s c1 c2
  addConstraint (rel s (inj1 c1) (inj2 c2) kind)
  return subst


-- Linear binding and a graded binding (likely from a promotion)
relateByAssumption s _ (idX, xc) (idY, yc) = do
  debugM "relateByAssumption" (pretty s <> ", " <> pretty idX <> ", " <> pretty idY)
  debugM "relateByAssumption" (pretty s <> ", " <> pretty xc <> ", " <> pretty yc)
  debugM "relateByAssumption" (pretty s <> ", " <> show xc <> ", " <> show yc)
  if idX == idY
    then throw UnifyGradedLinear{ errLoc = s, errLinearOrGraded = idX }
    else error $ "Internal bug: " <> pretty idX <> " does not match " <> pretty idY

-- Relate 3 assumptions by the least-upper bound relation, i.e.,
--   `relateByLUB s c1 c2 c3` means `c3` is the lub of `c1` and `c2`
-- Assumption that the three assumptions are for the same variable
relateByLUB :: (?globals :: Globals)
  => Span
  -> (Id, Assumption)
  -> (Id, Assumption)
  -> (Id, Assumption)
  -> Checker Substitution

-- Linear assumptions ignored
relateByLUB _ (_, Linear _) (_, Linear _) (_, Linear _) = return []

-- Discharged coeffect assumptions
relateByLUB s (_, Discharged _ c1) (_, Discharged _ c2) (_, Discharged _ c3) = do
  (kind, subst, (inj1, inj2)) <- mguCoeffectTypesFromCoeffects s c1 c2
  addConstraint (Lub s (inj1 c1) (inj2 c2) c3 kind True)
  return subst

-- TODO: handle new ghost variables
relateByLUB s (_, Ghost c1) (_, Ghost c2) (_, Ghost c3) = do
  (kind, subst, (inj1, inj2)) <- mguCoeffectTypesFromCoeffects s c1 c2
  addConstraint (Lub s (inj1 c1) (inj2 c2) c3 kind True)
  return subst

-- Linear binding and a graded binding (likely from a promotion)
relateByLUB s (idX, _) (idY, _) (_, _) =
  if idX == idY
    then throw UnifyGradedLinear{ errLoc = s, errLinearOrGraded = idX }
    else error $ "Internal bug: " <> pretty idX <> " does not match " <> pretty idY

-- `freshVarsIn names ctxt` creates a new context with
-- all the variables names in `ctxt` that appear in the list
-- `vars` and are discharged are
-- turned into discharged coeffect assumptions annotated
-- with a fresh coeffect variable (and all variables not in
-- `vars` get deleted).
-- Returns also the list of newly generated type variables
-- e.g.
--  `freshVarsIn ["x", "y"] [("x", Discharged (2, Int),
--                           ("y", Linear Int),
--                           ("z", Discharged (3, Int)]
--  -> ([("x", Discharged (c5 :: Nat, Int),
--      ("y", Linear Int)]
--     , [c5 :: Nat])
freshVarsIn :: (?globals :: Globals) => Span -> [Id] -> (Ctxt Assumption)
            -> Checker (Ctxt Assumption, Ctxt Kind)
freshVarsIn s vars ctxt = do
    newCtxtAndTyVars <- mapM toFreshVar (relevantSubCtxt vars ctxt)
    let (newCtxt, tyVars) = unzip newCtxtAndTyVars
    return (newCtxt, catMaybes tyVars)
  where
    toFreshVar :: (Id, Assumption) -> Checker ((Id, Assumption), Maybe (Id, Kind))
    toFreshVar (var, Discharged t c) = do
      -- TODO: deal with the subst here
      (ctype, _, _) <- synthKind s c
      -- Create a fresh variable
      freshName <- freshIdentifierBase (internalName var)
      let cvar = mkId freshName
      -- Update the coeffect kind context
      modify (\s -> s { tyVarContext = (cvar, (ctype, InstanceQ)) : tyVarContext s })

      -- Return the freshened var-type mapping
      -- and the new type variable
      return ((var, Discharged t (TyVar cvar)), Just (cvar, ctype))

    -- TODO: handle new ghost variables
    toFreshVar (var, Ghost c) = do
      (ctype, _, _) <- synthKind s c
      freshName <- freshIdentifierBase (internalName var)
      let cvar = mkId freshName
      modify (\s -> s { tyVarContext = (cvar, (ctype, InstanceQ)) : tyVarContext s })
      return ((var, Ghost (TyVar cvar)), Just (cvar, ctype))

    toFreshVar (var, Linear t) = return ((var, Linear t), Nothing)


-- Combine two contexts
ctxtPlus :: (?globals :: Globals) => Span -> Ctxt Assumption -> Ctxt Assumption
  -> Checker (Ctxt Assumption)
ctxtPlus _ [] ctxt2 = return ctxt2
ctxtPlus s ((i, v) : ctxt1) ctxt2 = do
  ctxt' <- extCtxt s ctxt2 i v
  ctxtPlus s ctxt1 ctxt'

-- ExtCtxt the context
extCtxt :: (?globals :: Globals) => Span -> Ctxt Assumption -> Id -> Assumption
  -> Checker (Ctxt Assumption)
extCtxt s ctxt var (Linear t) = do

  case lookup var ctxt of
    Just (Linear t') ->
       if t == t'
        then throw LinearityError{ errLoc = s, linearityMismatch = LinearUsedMoreThanOnce var }
        else throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = t' }
    Just (Discharged t' c) ->
       if t == t'
         then do
          (k, subst, cElaborated) <- synthKind s c
          return $ replace ctxt var (Discharged t (TyInfix TyOpPlus cElaborated (TyGrade (Just k) 1)))
         else throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = t' }
    Just (Ghost c) ->
       throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = ghostType }
    Nothing -> return $ (var, Linear t) : ctxt

extCtxt s ctxt var (Discharged t c) = do

  case lookup var ctxt of
    Just (Discharged t' c') ->
        if t == t'
        then return $ replace ctxt var (Discharged t' (TyInfix TyOpPlus c c'))
        else throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = t' }
    Just (Ghost c') ->
        throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = ghostType }
    Just (Linear t') ->
        if t == t'
        then do
          (k, subst, cElaborated) <- synthKind s c
          return $ replace ctxt var (Discharged t (TyInfix TyOpPlus cElaborated (TyGrade (Just k) 1)))
        else throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = t' }
    Nothing -> return $ (var, Discharged t c) : ctxt

extCtxt s ctxt var (Ghost c) = do
  let t = ghostType
  case lookup var ctxt of
    Just (Discharged t' c') ->
        throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = t' }
    Just (Ghost c') ->
        if t == ghostType
        then return $ replace ctxt var (Ghost (TyInfix TyOpJoin c c'))
        else throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = ghostType }
    Just (Linear t') ->
        throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = t' }
    Nothing -> return $ (var, Discharged t c) : ctxt

-- Helper, foldM on a list with at least one element
fold1M :: Monad m => (a -> a -> m a) -> [a] -> m a
fold1M _ []     = error "Must have at least one case"
fold1M f (x:xs) = foldM f x xs

justLinear :: [(a, Assumption)] -> [(a, Assumption)]
justLinear [] = []
justLinear ((x, Linear t) : xs) = (x, Linear t) : justLinear xs
justLinear ((x, _) : xs) = justLinear xs

checkGuardsForExhaustivity :: (?globals :: Globals)
  => Span -> Id -> Type -> [Equation () ()] -> Checker ()
checkGuardsForExhaustivity s name ty eqs = do
  debugM "Guard exhaustivity" "todo"
  return ()

checkGuardsForImpossibility :: (?globals :: Globals) => Span -> Id -> [Type] -> Checker ()
checkGuardsForImpossibility s name refinementConstraints = do
  -- Convert all universal variables to existential
  {- for example, if we are looking at the following program:
      from tests/cases/negative/impossibilityNat.gr

      data N (n : Nat) where
        Z : N 0;
        S : N n -> N (n + 1)

      pred : forall {n : Nat} . N (n + 1) -> N n
      pred (S n) = n;
      pred Z = Z

  -- We want this to be disallowed because the last pattern match is always impossible
  -- i.e., there exists no such `n` such that `n + 1 = 0`.
  -- Thus, to do this check we first make every universally quantified variable into an
  -- existential (a unification variable)
  -}

  tyVars <- tyVarContextExistential >>= includeOnlyGradeVariables s

  -- Get top of guard predicate stack
  st <- get
  let guardPredicatesStack = head $ guardPredicates st
  debugM "guardPredicatesStack" (pretty $ guardPredicates st)

  -- Convert all universal variables to existential
  tyVars <- tyVarContextExistential >>= includeOnlyGradeVariables s

  -- For each guard predicate
  forM_ guardPredicatesStack $ \((ctxt, predicate), s) -> do

    -- Existentially quantify those variables occuring in the pattern in scope
    -- TODO: Remvoe commented code
    -- constraints' <- mapM (compileTypeConstraintToConstraint nullSpanNoFile) refinementConstraints
    let theorem = foldr (uncurry Exists) predicate ctxt
    theorem <- handleHsupPoly tyVars theorem

    debugM "impossibility" $ "about to try (" <> pretty tyVars <> ") . " <> pretty theorem
    -- Try to prove the theorem
    constructors <- allDataConstructorNames
    (_, result) <- liftIO $ provePredicate theorem tyVars constructors

    case result of
      QED -> return ()

      -- Various kinds of error
      -- TODO make errors better
      NotValid msg -> do
            theorem' <- simplifyPred theorem
            throw ImpossiblePatternMatch
                { errLoc = s
                , errId = name
                , errPred = theorem'
                }
      NotValidTrivial unsats ->
        throw ImpossiblePatternMatchTrivial
          { errLoc = s
          , errId = name
          , errUnsats = unsats
          }
      Timeout -> do
            theorem' <- simplifyPred theorem
            throw SolverTimeout
              { errLoc = s
              , errDefId = name
              , errSolverTimeoutMillis = solverTimeoutMillis
              , errContext = "pattern match of an equation"
              , errPred = theorem'
              }

      OtherSolverError msg -> do
            theorem' <- simplifyPred theorem
            throw ImpossiblePatternMatch
                    { errLoc = s
                    , errId = name
                    , errPred = theorem'
                    }

      SolverProofError msg -> error msg

--
-- For use in impossibility checking,
-- make true a `Hsup r s` constraint
-- where `r` and `s` are unification variables
-- whose kind is also a unification variable, i.e., this is capturing
-- a polymorphic constraint here.
handleHsupPoly :: (?globals :: Globals) => Ctxt (Type, Quantifier) -> Pred -> Checker Pred
-- match on `HSup r s` - handle the main cases here.
handleHsupPoly localCtxt c@(Con (Hsup s (TyVar v1) (TyVar v2) (TyVar t))) = do
  st <- get
  let ctxt = localCtxt ++ tyVarContext st
  case (lookup v1 ctxt, lookup v2 ctxt, lookup t ctxt) of
    (Just (TyVar t1, InstanceQ), Just (TyVar t2, InstanceQ), Just (_, ForallQ)) ->
        -- rewrite to True
        return $ Conj []
    _ -> return c

handleHsupPoly localCtxt (Con con) = return (Con con)

handleHsupPoly localCtxt (Conj ps) =
  Conj <$> mapM (handleHsupPoly localCtxt) ps

handleHsupPoly localCtxt (Disj ps) =
  Disj <$> mapM (handleHsupPoly localCtxt) ps

handleHsupPoly localCtxt (Impl ctxt p1 p2) =
  (Impl ctxt) <$> (handleHsupPoly localCtxt p1) <*> (handleHsupPoly localCtxt p2)

handleHsupPoly localCtxt (Exists v k p) =
  (Exists v k) <$> (handleHsupPoly ((v, (k, InstanceQ)) : localCtxt) p)

-- Don't go inside negation
handleHsupPoly _ (NegPred p) =
  return $ NegPred p

freshenTySchemeForVar :: (?globals :: Globals) => Span -> Bool -> Id -> TypeScheme -> Checker (Type, Ctxt Assumption, Substitution, Expr () Type)
freshenTySchemeForVar s rf id tyScheme = do
  (ty', _, constraints, []) <- freshPolymorphicInstance InstanceQ False tyScheme [] [] -- discard list of fresh type variables

  otherTypeConstraints <- enforceConstraints s constraints
  registerWantedTypeConstraints otherTypeConstraints

  let elaborated = Val s ty' rf (Var ty' id)
  return (ty', [], [], elaborated)


-- Classified those expressions which are resource allocators
resourceAllocator :: Expr a t -> Bool
resourceAllocator (Val _ _ _ (Var _ p)) =
    internalName p `elem` Primitives.unpromotables
resourceAllocator (Val _ _ _ (Promote _ e)) =
    resourceAllocator e
resourceAllocator (App _ _ _ e1 e2) =
    resourceAllocator e1 || resourceAllocator e2
resourceAllocator (AppTy _ _ _ e _) =
    resourceAllocator e
resourceAllocator (Binop _ _ _ _ e1 e2) =
    resourceAllocator e1 || resourceAllocator e2
resourceAllocator (Case _ _ _ eg cases) =
    resourceAllocator eg || any (resourceAllocator . snd) cases
resourceAllocator (TryCatch _ _ _ e1 _ _ e2 e3) =
    resourceAllocator e1 || resourceAllocator e2 || resourceAllocator e3
resourceAllocator _ = False

applySubstitutionsOnGuardPredicates :: (?globals::Globals) => Span -> [Substitution] -> Checker ()
applySubstitutionsOnGuardPredicates s substs = do
  modifyM (\st -> do
                subst <- combineManySubstitutions s substs
                guardPreds' <- mapM (mapM (\((ctxt, pred), sp) -> do
                  ctxt' <- substitute subst ctxt
                  pred' <- substitute subst pred
                  return ((ctxt', pred'), sp))) (guardPredicates st)
                return (st { guardPredicates = guardPreds' }))