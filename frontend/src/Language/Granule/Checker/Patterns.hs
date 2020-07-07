{-# LANGUAGE ImplicitParams #-}
{-# options_ghc -fno-warn-incomplete-uni-patterns #-}

module Language.Granule.Checker.Patterns where

import Control.Monad.Except (throwError)
import Control.Monad.State.Strict
import Data.List (transpose)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (fromMaybe, listToMaybe)

import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Types (equalTypesRelatedCoeffectsAndUnify, SpecIndicator(..))
import Language.Granule.Checker.Flatten
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Kinds
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.Variables

import Language.Granule.Context
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Helpers (freeVars)
import Language.Granule.Utils

-- | Creates a constraint when a definition unification has occured under
--   a box pattern (or many nested box patterns)
definiteUnification :: (?globals :: Globals)
  => Span
  -> Maybe (Coeffect, Type) -- Outer coeffect
  -> Type                   -- Type of the pattern
  -> Checker ()
definiteUnification _ Nothing _ = return ()
definiteUnification s (Just (coeff, coeffTy)) ty = do
  isPoly <- polyShaped ty
  when isPoly $ -- Used to be: addConstraintToPreviousFrame, but paper showed this was not a good idea
    addConstraint $ ApproximatedBy s (COne coeffTy) coeff coeffTy

-- | Predicate on whether a type has more than 1 shape (constructor)
polyShaped :: (?globals :: Globals) => Type -> Checker Bool
polyShaped t = case leftmostOfApplication t of
    TyCon k -> do
      mCardinality <- lookup k <$> gets typeConstructors
      case mCardinality of
        Just (_, c, _) -> case length c of
          1 -> do
            debugM "uniShaped constructor" (show t <> "\n" <> show c)
            pure False
          _ -> do
            debugM "polyShaped constructor" (show t <> "\n" <> show c)
            pure True
        Nothing -> error $ mconcat
          [ "Internal checker error, tried to look up nonexistent type "
          , show k
          , " in context." ]
    _ -> do
      debugM "polyShaped because not a constructor" (show t)
      pure True

-- Given two patterns, finds which predicates annotated on the latter should be
-- propagated forward.
extractFromPattern :: Pattern a -> Pattern b -> [b]
-- We always propagate forward theorems from constants.
extractFromPattern _ (PInt _ p _ _) = return p
extractFromPattern _ (PFloat _ p _ _) = return p
-- With a constructor, we propagate, unless they are the same constructor, in
-- which case we recurse on the subpatterns.
extractFromPattern (PConstr _ _ _ id1 sub1) (PConstr _ p _ id2 sub2)
  | id1 == id2 = concat $ zipWith extractFromPattern sub1 sub2
  | otherwise = return p
extractFromPattern _ (PConstr _ p _ _ _) = return p
-- Similarly, for unboxings we also propagate forward unless both patterns are
-- unboxings, in which case we recurse.
extractFromPattern (PBox _ _ _ sub1) (PBox _ _ _ sub2) = extractFromPattern sub1 sub2
extractFromPattern _ (PBox _ p _ _) = return p
-- In any other case, there is nothing to propagate.
extractFromPattern _ _ = []

-- | Given a pattern and its type, construct Just of the binding context
--   for that pattern, or Nothing if the pattern is not well typed
--   Returns also:
--      - a context of any variables bound by the pattern
--        (e.g. for dependent matching) with their kinds
--      - a substitution for variables
--           caused by pattern matching (e.g., from unification),
--      - a consumption context explaining usage triggered by pattern matching
ctxtFromTypedPattern :: (?globals :: Globals) =>
  Span
  -> Type
  -> Pattern ()
  -> Consumption   -- Consumption behaviour of the patterns in this position so far
  -> Checker (Ctxt Assumption, Ctxt Kind, Substitution, Pattern Type, Pattern (Ctxt Kind, Pred), Consumption)

ctxtFromTypedPattern = ctxtFromTypedPattern' Nothing

-- | Inner helper, which takes information about the enclosing coeffect
ctxtFromTypedPattern' :: (?globals :: Globals) =>
     Maybe (Coeffect, Type)    -- enclosing coeffect
  -> Span
  -> Type
  -> Pattern ()
  -> Consumption   -- Consumption behaviour of the patterns in this position so far
  -> Checker (Ctxt Assumption, Ctxt Kind, Substitution, Pattern Type, Pattern (Ctxt Kind, Pred), Consumption)

-- Pattern matching on wild cards and variables (linear)
ctxtFromTypedPattern' outerCoeff _ t p@(PWild s _ rf) cons = do
    -- DESIGN DECISION: We've turned off the checks that our linearity for ints
    -- when preceded by other concrete matches. (15/02/19) - DAO
    -- But we want to think about this more in the future

    --case cons of
      -- Full consumption is allowed here
    --  Full -> do

        -- If the wildcard appears under one or more [ ] pattern then we must
        -- add a constraint that 0 approaximates the effect of the enclosing
        -- box patterns.
        let elabP = PWild s t rf

        case outerCoeff of
          -- Can only have a wildcard not under a box if the type of the pattern is unishaped
          Nothing -> do
            isPoly <- polyShaped t
            if isPoly
              then illLinearityMismatch s (pure NonLinearPattern)
              else do
                let predP = PWild s ([], Conj []) rf
                return ([], [], [], elabP, predP, Full)

          Just (coeff, coeffTy) -> do
              -- Must approximate zero
              let constr = ApproximatedBy s (CZero coeffTy) coeff coeffTy
              addConstraint constr
              let predP = PWild s ([], Conj [Con constr]) rf
              return ([], [], [], elabP, predP, NotFull)

  --  _ -> illLinearityMismatch s [NonLinearPattern]

ctxtFromTypedPattern' outerCoeff _ t (PVar s _ rf v) _ = do
    let elabP = PVar s t rf v
    let predP = PVar s ([], Conj []) rf v

    case outerCoeff of
      Nothing ->
         return ([(v, Linear t)], [], [], elabP, predP, NotFull)
      Just (coeff, _) ->
         return ([(v, Discharged t coeff)], [], [], elabP, predP, NotFull)

-- Pattern matching on constarints
ctxtFromTypedPattern' outerCoeff s ty@(TyCon c) (PInt s' _ rf n) _
  | internalName c == "Int" = do

    newConjunct
    definiteUnification s outerCoeff ty
    pred <- squashPred

    let elabP = PInt s' ty rf n
    let predP = PInt s' ([], pred) rf n
    return ([], [], [], elabP, predP, Full)

ctxtFromTypedPattern' outerCoeff s ty@(TyCon c) (PFloat s' _ rf n) _
  | internalName c == "Float" = do

    newConjunct
    definiteUnification s outerCoeff ty
    pred <- squashPred

    let elabP = PFloat s' ty rf n
    let predP = PFloat s' ([], pred) rf n
    return ([], [], [], elabP, predP, Full)

-- Pattern match on a modal box
ctxtFromTypedPattern' outerBoxTy s t@(Box coeff ty) pat@(PBox sp _ rf p) _ = do

    (innerBoxTy, subst0) <- inferCoeffectType s coeff

    (coeff, subst1, coeffTy) <- case outerBoxTy of
        -- Case: no enclosing [ ] pattern
        Nothing -> return (coeff, [], innerBoxTy)
        -- Case: there is an enclosing [ ] pattern of type outerBoxTy
        Just (outerCoeff, outerBoxTy) -> do
          -- Therefore try and flatten at this point
          flatM <- flattenable outerBoxTy innerBoxTy
          case flatM of
            Just (flattenOp, subst, ty) -> return (flattenOp outerCoeff coeff, subst, ty)
            Nothing -> throw DisallowedCoeffectNesting
              { errLoc = s, errTyOuter = outerBoxTy, errTyInner = innerBoxTy }

    newConjunct
    (ctxt, eVars, subst, elabPInner, predPInner, consumption) <- ctxtFromTypedPattern' (Just (coeff, coeffTy)) s ty p Full
    pred <- squashPred

    let elabP = PBox sp t rf elabPInner
    let predP = PBox sp ([], pred) rf predPInner
    substU <- combineManySubstitutions s [subst0, subst1, subst]
    return (ctxt, eVars, substU, elabP, predP, NotFull)

ctxtFromTypedPattern' outerBoxTy _ ty p@(PConstr s _ rf dataC ps) cons = do
  debugM "Patterns.ctxtFromTypedPattern" $ "ty: " <> show ty <> "\t" <> pretty ty <> "\nPConstr: " <> pretty dataC

  st <- get
  mConstructor <- lookupDataConstructor s dataC
  case mConstructor of
    Nothing -> throw UnboundDataConstructor{ errLoc = s, errId = dataC }
    Just (tySch, coercions) -> do
      newConjunct
      definiteUnification s outerBoxTy ty

      (dataConstructorTypeFresh, freshTyVarsCtxt, freshTyVarSubst, constraints, coercions') <-
          freshPolymorphicInstance BoundQ True tySch coercions

      mapM_ (\ty -> do
        pred <- compileTypeConstraintToConstraint s ty
        addPredicate pred) constraints

      -- Debugging
      debugM "ctxt" $ "### DATA CONSTRUCTOR (" <> pretty dataC <> ")"
                         <> "\n###\t tySch = " <> pretty tySch
                         <> "\n###\t coercions =  " <> show coercions
                         <> "\n###\n"
      debugM "ctxt" $ "\n### FRESH POLY ###\n####\t dConTyFresh = "
                      <> show dataConstructorTypeFresh
                      <> "\n###\t ctxt = " <> show freshTyVarsCtxt
                      <> "\n###\t freshTyVarSubst = " <> show freshTyVarSubst
                      <> "\n###\t coercions' =  " <> show coercions'

      dataConstructorTypeFresh <- substitute (flipSubstitution coercions') dataConstructorTypeFresh

      st <- get
      debugM "ctxt" $ "### tyVarContext = " <> show (tyVarContext st)
      debugM "ctxt" $ "\t### eqL (res dCfresh) = " <> show (resultType dataConstructorTypeFresh) <> "\n"
      debugM "ctxt" $ "\t### eqR (ty) = " <> show ty <> "\n"

      debugM "Patterns.ctxtFromTypedPattern" $ pretty dataConstructorTypeFresh <> "\n" <> pretty ty
      areEq <- equalTypesRelatedCoeffectsAndUnify s Eq PatternCtxt (resultType dataConstructorTypeFresh) ty
      case areEq of
        (True, _, unifiers) -> do

          -- Register coercions as equalities
          mapM_ (\(var, SubstT ty) ->
                        equalTypesRelatedCoeffectsAndUnify s Eq PatternCtxt (TyVar var) ty) coercions'

          dataConstructorIndexRewritten <- substitute unifiers dataConstructorTypeFresh
          dataConstructorIndexRewrittenAndSpecialised <- substitute coercions' dataConstructorIndexRewritten

          -- Debugging
          debugM "ctxt" $ "\n\t### unifiers = " <> show unifiers <> "\n"
          debugM "ctxt" $ "### dfresh = " <> show dataConstructorTypeFresh
          debugM "ctxt" $ "### drewrit = " <> show dataConstructorIndexRewritten
          debugM "ctxt" $ "### drewritAndSpec = " <> show dataConstructorIndexRewrittenAndSpecialised <> "\n"

          pred <- squashPred
          let relevantVars = relevantSubCtxt (freeVars pred) freshTyVarsCtxt

          (as, bs, us, elabPs, predPs, consumptionOut) <- unpeel ps dataConstructorIndexRewrittenAndSpecialised

          -- Combine the substitutions
          subst <- combineSubstitutions s (flipSubstitution unifiers) us
          subst <- combineSubstitutions s coercions' subst
          debugM "ctxt" $ "\n\t### outSubst = " <> show subst <> "\n"

          -- (ctxtSubbed, ctxtUnsubbed) <- substCtxt subst as
          
          let elabP = PConstr s ty rf dataC elabPs
          let predP = PConstr s (relevantVars, pred) rf dataC predPs

          return (as, -- ctxtSubbed <> ctxtUnsubbed,     -- concatenate the contexts
                  freshTyVarsCtxt <> bs,          -- concat the context of new type variables
                  subst,                          -- returned the combined substitution
                  elabP,                          -- elaborated pattern
                  predP,                          -- pattern with predicates
                  consumptionOut)                 -- final consumption effect

        _ -> throw PatternTypingMismatch
              { errLoc = s
              , errPat = p
              , tyExpected = dataConstructorTypeFresh
              , tyActual = ty
              }
  where
    unpeel :: [Pattern ()] -- A list of patterns for each part of a data constructor pattern
            -> Type -- The remaining type of the constructor
            -> Checker (Ctxt Assumption, Ctxt Kind, Substitution, [Pattern Type], [Pattern (Ctxt Kind, Pred)], Consumption)
    unpeel = unpeel' ([], [], [], [], [], Full)

    -- Tail recursive version of unpeel
    unpeel' acc [] t = return acc

    unpeel' (as, bs, us, elabPs, predPs, consOut) (p:ps) (FunTy _ t t') = do
        (as', bs', us', elabP, predP, consOut') <- ctxtFromTypedPattern' outerBoxTy s t p cons
        us <- combineSubstitutions s us us'
        unpeel' (as <> as', bs <> bs', us, elabPs ++ [elabP], predPs ++ [predP], consOut `meetConsumption` consOut') ps t'

    unpeel' _ (p:_) t = throw PatternArityError{ errLoc = s, errId = dataC }

ctxtFromTypedPattern' _ s t p _ = do
  st <- get
  debugM "ctxtFromTypedPattern" $ "Type: " <> show t <> "\nPat: " <> show p
  debugM "dataConstructors in checker state" $ show $ dataConstructors st
  throw PatternTypingError{ errLoc = s, errPat = p, tyExpected = t }

ctxtFromTypedPatterns :: (?globals :: Globals)
  => Span
  -> Type
  -> [Pattern ()]
  -> [Consumption]
  -> Checker (Ctxt Assumption, Type, Ctxt Kind, Substitution, [Pattern Type], [Consumption])
ctxtFromTypedPatterns sp ty pats cons = do
  st <- get
  let prevPatterns = transpose (prevPatternPreds st)
  modify (\st -> st { prevPatternPreds = [] : prevPatternPreds st})
  ctxtFromTypedPatterns' sp ty pats cons prevPatterns

ctxtFromTypedPatterns' :: (?globals :: Globals)
  => Span
  -> Type
  -> [Pattern ()]
  -> [Consumption]
  -> [[Pattern (Ctxt Kind, Pred)]]
  -> Checker (Ctxt Assumption, Type, Ctxt Kind, Substitution, [Pattern Type], [Consumption])
ctxtFromTypedPatterns' sp ty [] _ _ = do
  return ([], ty, [], [], [], [])

ctxtFromTypedPatterns' s (FunTy _ t1 t2) (pat:pats) (cons:consumptionsIn) prevPatss = do
  -- Match a pattern
  (localGam, eVars, subst, elabP, predP, consumption) <- ctxtFromTypedPattern s t1 pat cons

  -- Propagate relevant theorems
  st <- get
  let relevant = concatMap (extractFromPattern pat) (fromMaybe [] (listToMaybe prevPatss))
  -- Associate each propagated predicate with a source location.
  let withSpan = map (\r -> (r, s)) relevant
  -- Add the predicates to the top of the guardPredicates stack.
  let guardPredicates' =
        case guardPredicates st of
          (head:tail) -> (head ++ withSpan) : tail
          [] -> [withSpan]
  let prevPatternPreds' =
        case prevPatternPreds st of
          (current:rest) -> (current ++ [predP]) : rest
          [] -> [[predP]]

  modify (\st -> st
      { prevPatternPreds = prevPatternPreds'
      , guardPredicates = guardPredicates' })
  st <- get

  -- Match the rest
  (localGam', ty, eVars', substs, elabPs, consumptions) <-
      ctxtFromTypedPatterns' s t2 pats consumptionsIn (drop 1 prevPatss)

  -- Combine the results
  substs' <- combineSubstitutions s subst substs
  return (localGam <> localGam', ty, eVars ++ eVars', substs', elabP : elabPs, consumption : consumptions)

ctxtFromTypedPatterns' s ty (p:ps) _ _ = do
  -- This means we have patterns left over, but the type is not a
  -- function type, so we need to throw a type error

  -- First build a representation of what the type would look like
  -- if this was well typed, i.e., if we have two patterns left we get
  -- p0 -> p1 -> ?
  psTyVars <- mapM (\_ -> freshIdentifierBase "?" >>= return . TyVar . mkId) ps
  let spuriousType = foldr (FunTy Nothing) (TyVar $ mkId "?") psTyVars
  throw TooManyPatternsError
    { errLoc = s, errPats = p :| ps, tyExpected = ty, tyActual = spuriousType }

duplicateBinderCheck :: Span -> [Pattern a] -> Checker ()
duplicateBinderCheck s ps = case duplicateBinders of
  [] -> pure ()
  (d:ds) ->
    throwError $ fmap (DuplicateBindingError s) (d :| ds)
  where
    duplicateBinders = duplicates . concatMap getBinders $ ps
    getBinders = patternFold
      (\_ _ _ id -> [sourceName id])
      (\_ _ _ -> [])
      (\_ _ _ bs -> bs)
      (\_ _ _ _ -> [])
      (\_ _ _ _ -> [])
      (\_ _ _ _ bss -> concat bss)

-- | Folds the top conjunct into the next one (creating one big conjunct), while
--   returning the top conjunct.
squashPred :: Checker Pred
squashPred = do
  st <- get
  case predicateStack st of
    (Conj xs : Conj ys : ps) -> do
      modify (\st -> st { predicateStack = Conj (xs ++ ys) : ps })
      return $ Conj xs
    (Conj xs : ps) -> return $ Conj xs
    _ -> return $ Conj []
