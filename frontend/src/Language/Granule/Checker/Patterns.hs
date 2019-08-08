{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}
{-# options_ghc -fno-warn-incomplete-uni-patterns #-}

module Language.Granule.Checker.Patterns where

import Control.Monad.Except (throwError)
import Control.Monad.State.Strict
import Data.List.NonEmpty (NonEmpty(..))

import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Types (equalTypesRelatedCoeffectsAndUnify, SpecIndicator(..))
import Language.Granule.Checker.Coeffects
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Kinds
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.Variables

import Language.Granule.Context
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Pretty
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
        Just (_, c) -> case c of
          Just 1 -> do
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
  -> Checker (Ctxt Assumption, Ctxt Kind, Substitution, Pattern Type, Consumption)

ctxtFromTypedPattern = ctxtFromTypedPattern' Nothing

-- | Inner helper, which takes information about the enclosing coeffect
ctxtFromTypedPattern' :: (?globals :: Globals) =>
     Maybe (Coeffect, Type)    -- enclosing coeffect
  -> Span
  -> Type
  -> Pattern ()
  -> Consumption   -- Consumption behaviour of the patterns in this position so far
  -> Checker (Ctxt Assumption, Ctxt Kind, Substitution, Pattern Type, Consumption)

-- Pattern matching on wild cards and variables (linear)
ctxtFromTypedPattern' outerCoeff _ t (PWild s _) cons =
    -- DESIGN DECISION: We've turned off the checks that our linearity for ints
    -- when preceded by other concrete matches. (15/02/19) - DAO
    -- But we want to think about this more in the future

    --case cons of
      -- Full consumption is allowed here
    --  Full -> do

        -- If the wildcard appears under one or more [ ] pattern then we must
        -- add a constraint that 0 approaximates the effect of the enclosing
        -- box patterns.
        case outerCoeff of
          -- Can only have a wildcard under a box if the type of the pattern is unishaped
          Nothing -> do
            isPoly <- polyShaped t
            if isPoly
              then illLinearityMismatch s (pure NonLinearPattern)
              else return ([], [], [], PWild s t, Full)

          Just (coeff, coeffTy) -> do
              -- Must approximate zero
              addConstraint $ ApproximatedBy s (CZero coeffTy) coeff coeffTy

              return ([], [], [], PWild s t, NotFull)

  --  _ -> illLinearityMismatch s [NonLinearPattern]

ctxtFromTypedPattern' outerCoeff _ t (PVar s _ v) _ = do
    let elabP = PVar s t v

    case outerCoeff of
      Nothing ->
         return ([(v, Linear t)], [], [], elabP, NotFull)
      Just (coeff, _) ->
         return ([(v, Discharged t coeff)], [], [], elabP, NotFull)

-- Pattern matching on constarints
ctxtFromTypedPattern' outerCoeff s ty@(TyCon c) (PInt s' _ n) _
  | internalName c == "Int" = do

    definiteUnification s outerCoeff ty

    let elabP = PInt s' ty n
    return ([], [], [], elabP, Full)

ctxtFromTypedPattern' outerCoeff s ty@(TyCon c) (PFloat s' _ n) _
  | internalName c == "Float" = do

    definiteUnification s outerCoeff ty

    let elabP = PFloat s' ty n
    return ([], [], [], elabP, Full)

-- Pattern match on a modal box
ctxtFromTypedPattern' outerBoxTy s t@(Box coeff ty) (PBox sp _ p) _ = do

    innerBoxTy <- inferCoeffectType s coeff

    (coeff, coeffTy) <- case outerBoxTy of
        -- Case: no enclosing [ ] pattern
        Nothing -> return (coeff, innerBoxTy)
        -- Case: there is an enclosing [ ] pattern of type outerBoxTy
        Just (outerCoeff, outerBoxTy) ->
          -- Therefore try and flatten at this point
          case flattenable outerBoxTy innerBoxTy of
            Just (flattenOp, ty) -> return (flattenOp outerCoeff coeff, ty)
            Nothing -> throw DisallowedCoeffectNesting
              { errLoc = s, errTyOuter = outerBoxTy, errTyInner = innerBoxTy }


    (ctxt, eVars, subst, elabPinner, consumption) <- ctxtFromTypedPattern' (Just (coeff, coeffTy)) s ty p Full

    let elabP = PBox sp t elabPinner
    return (ctxt, eVars, subst, elabP, NotFull)

ctxtFromTypedPattern' outerBoxTy _ ty p@(PConstr s _ dataC ps) cons = do
  debugM "Patterns.ctxtFromTypedPattern" $ "ty: " <> show ty <> "\t" <> pretty ty <> "\nPConstr: " <> pretty dataC

  st <- get
  mConstructor <- lookupDataConstructor s dataC
  case mConstructor of
    Nothing -> throw UnboundDataConstructor{ errLoc = s, errId = dataC }
    Just (tySch, coercions) -> do

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

          (as, bs, us, elabPs, consumptionOut) <- unpeel ps dataConstructorIndexRewrittenAndSpecialised

          -- Combine the substitutions
          subst <- combineSubstitutions s (flipSubstitution unifiers) us
          subst <- combineSubstitutions s coercions' subst
          debugM "ctxt" $ "\n\t### outSubst = " <> show subst <> "\n"

          -- (ctxtSubbed, ctxtUnsubbed) <- substCtxt subst as

          let elabP = PConstr s ty dataC elabPs
          return (as, -- ctxtSubbed <> ctxtUnsubbed,     -- concatenate the contexts
                  freshTyVarsCtxt <> bs,          -- concat the context of new type variables
                  subst,                          -- returned the combined substitution
                  elabP,                          -- elaborated pattern
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
            -> Checker (Ctxt Assumption, Ctxt Kind, Substitution, [Pattern Type], Consumption)
    unpeel = unpeel' ([],[],[],[],Full)

    -- Tail recursive version of unpeel
    unpeel' acc [] t = return acc

    unpeel' (as,bs,us,elabPs,consOut) (p:ps) (FunTy t t') = do
        (as',bs',us',elabP, consOut') <- ctxtFromTypedPattern' outerBoxTy s t p cons
        us <- combineSubstitutions s us us'
        unpeel' (as<>as', bs<>bs', us, elabP:elabPs, consOut `meetConsumption` consOut') ps t'

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
ctxtFromTypedPatterns sp ty [] _ = do
  return ([], ty, [], [], [], [])

ctxtFromTypedPatterns s (FunTy t1 t2) (pat:pats) (cons:consumptionsIn) = do

  -- Match a pattern
  (localGam, eVars, subst, elabP, consumption) <- ctxtFromTypedPattern s t1 pat cons

  -- Match the rest
  (localGam', ty, eVars', substs, elabPs, consumptions) <-
      ctxtFromTypedPatterns s t2 pats consumptionsIn

  -- Combine the results
  substs' <- combineSubstitutions s subst substs
  return (localGam <> localGam', ty, eVars ++ eVars', substs', elabP : elabPs, consumption : consumptions)

ctxtFromTypedPatterns s ty (p:ps) _ = do
  -- This means we have patterns left over, but the type is not a
  -- function type, so we need to throw a type error

  -- First build a representation of what the type would look like
  -- if this was well typed, i.e., if we have two patterns left we get
  -- p0 -> p1 -> ?
  psTyVars <- mapM (\_ -> freshIdentifierBase "?" >>= return . TyVar . mkId) ps
  let spuriousType = foldr FunTy (TyVar $ mkId "?") psTyVars
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
      (\_ _ id -> [sourceName id])
      (\_ _ -> [])
      (\_ _ bs -> bs)
      (\_ _ _ -> [])
      (\_ _ _ -> [])
      (\_ _ _ bss -> concat bss)
