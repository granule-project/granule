{-# LANGUAGE ImplicitParams #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

{-# options_ghc -fno-warn-incomplete-uni-patterns #-}

-- | Type checking patterns
module Language.Granule.Checker.Patterns where

import Control.Monad.Except (throwError)
import Control.Monad.State.Strict
import Data.List.NonEmpty (NonEmpty(..))

import Language.Granule.Checker.Coeffects
import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Types (equalTypesRelatedCoeffectsAndUnify, SpecIndicator(..))
import Language.Granule.Checker.Ghost
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Kinding
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Variables
import Language.Granule.Checker.Normalise

import Language.Granule.Context
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Pretty
import Language.Granule.Utils
import qualified Data.Functor

-- | Creates a constraint when a definition unification has occured under
--   a box pattern (or many nested box patterns)
definiteUnification :: (?globals :: Globals)
  => Span
  -> PatternPosition
  -> Maybe (Coeffect, Type) -- Outer coeffect
  -> Type                   -- Type of the pattern
  -> Checker ()
definiteUnification _ _ Nothing _ = return ()
definiteUnification s pos (Just (coeff, coeffTy)) ty = do
  isPoly <- polyShaped ty
  -- TODO: simplify
  when isPoly $ -- Used to be: addConstraintToPreviousFrame, but paper showed this was not a good idea
    case pos of
      InCase             -> addConstraintToNextFrame $ ApproximatedBy s (TyGrade (Just coeffTy) 1) coeff coeffTy
      InFunctionEquation -> addConstraintToNextFrame $ ApproximatedBy s (TyGrade (Just coeffTy) 1) coeff coeffTy

-- | Predicate on whether a type has more than 1 shape (constructor)
polyShaped :: (?globals :: Globals) => Type -> Checker Bool
polyShaped t =
  case leftmostOfApplication t of
    TyCon k -> do
      mCardinality <- lookup k <$> gets typeConstructors
      case mCardinality of
        Just (_, c, _) -> case length c of
          1 -> do
            debugM "monoShaped constructor" (show t <> "\n" <> show c)
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

data PatternPosition = InCase | InFunctionEquation

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
  -> PatternPosition -- is this a case or a top-level equation
  --                   -- (additional equations in a case get registered
  --                   -- in the preceding predicate frame rather than as part of an implication
  --                   -- as we know they need to be checked now.
  -> Type
  -> Pattern ()
  -> Consumption   -- Consumption behaviour of the patterns in this position so far
  -> Checker (Ctxt Assumption, Ctxt Kind, Substitution, Pattern Type, Consumption)

ctxtFromTypedPattern = ctxtFromTypedPattern' Nothing

-- | Inner helper, which takes information about the enclosing coeffect
ctxtFromTypedPattern' :: (?globals :: Globals) =>
     Maybe (Coeffect, Type)    -- enclosing coeffect
  -> Span
  -> PatternPosition
  -> Type
  -> Pattern ()
  -> Consumption   -- Consumption behaviour of the patterns in this position so far
  -> Checker (Ctxt Assumption, Ctxt Kind, Substitution, Pattern Type, Consumption)

-- Pattern matching on wild cards and variables (linear)
ctxtFromTypedPattern' outerCoeff _ pos t (PWild s _ rf) cons =
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
          -- Can only have a wildcard not under a box if the type of the pattern is unishaped
          Nothing -> do
            isPoly <- polyShaped t
            if isPoly
              then illLinearityMismatch s (pure NonLinearPattern)
              else return ([], [], [], PWild s t rf, Full)

          Just (coeff, coeffTy) -> do
              -- Must approximate zero
              case pos of
                InFunctionEquation -> addConstraintToNextFrame $ ApproximatedBy s (TyGrade (Just coeffTy) 0) coeff coeffTy
                InCase             -> addConstraintToNextFrame $ ApproximatedBy s (TyGrade (Just coeffTy) 0) coeff coeffTy

              return ([], [], [], PWild s t rf, NotFull)

  --  _ -> illLinearityMismatch s [NonLinearPattern]

ctxtFromTypedPattern' outerCoeff _ _ t (PVar s _ rf v) _ = do
    let elabP = PVar s t rf v

    case outerCoeff of
      Nothing ->
         return ([(v, Linear t)], [], [], elabP, NotFull)
      Just (coeff, _) ->
         return ([(v, Discharged t coeff)], [], [], elabP, NotFull)

-- Pattern matching on constarints
ctxtFromTypedPattern' outerCoeff s pos ty@(TyCon c) (PInt s' _ rf n) _
  | internalName c == "Int" = do

    definiteUnification s pos outerCoeff ty

    let elabP = PInt s' ty rf n
    return ([], [], [], elabP, Full)

ctxtFromTypedPattern' outerCoeff s pos ty@(TyCon c) (PFloat s' _ rf n) _
  | internalName c == "Float" = do

    definiteUnification s pos outerCoeff ty

    let elabP = PFloat s' ty rf n
    return ([], [], [], elabP, Full)

-- Pattern match on a modal box
ctxtFromTypedPattern' outerCoeffAndTy s pos t@(Box coeff ty) (PBox sp _ rf p) _ = do
    (innerCoeffTy, subst0, _) <- synthKind s coeff
    -- Flatten with outter coeffect, if there is one
    (Just (coeff, coeffTy), subst1) <- flattenCoeffects s outerCoeffAndTy (Just (coeff, innerCoeffTy))

    (ctxt, eVars, subst, elabPinner, consumption) <- ctxtFromTypedPattern' (Just (coeff, coeffTy)) s pos ty p Full

    let elabP = PBox sp t rf elabPinner
    substU <- combineManySubstitutions s [subst0, subst1, subst]
    return (ctxt, eVars, substU, elabP, NotFull)

ctxtFromTypedPattern' outerBoxTy _ pos ty p@(PConstr s _ rf dataC tyVarBindsRequested ps) cons = do
  debugM "Patterns.ctxtFromTypedPattern" $ "ty: " <> show ty <> "\t" <> pretty ty <> "\nPConstr: " <> pretty dataC

  reportM $ "Typing pattern " <> prettyNested p <> " at type " <> prettyNested ty
  reportMsep

  st <- get
  mConstructor <- lookupDataConstructor s dataC
  case mConstructor of
    Nothing -> throw UnboundDataConstructor{ errLoc = s, errId = dataC }
    Just (tySch@(Forall _ tyVarBinders _ innerType), coercions, indices) -> do

      -- Check pattern arity
      if (arity innerType /= length ps)
        then throw $ PatternArityError s dataC (arity innerType) (length ps)
        else return ()

      case outerBoxTy of
        -- Hsup if you only have more than one premise (and have an enclosing grade)
        Just (coeff, coeffTy) | length ps > 1 ->
          addConstraintToNextFrame (Hsup s coeff coeff coeffTy)
        _ -> return ()

      -- get fresh instance of the data constructors type
      (dataConstructorTypeFresh, freshTyVarsCtxt, constraints, coercions') <-
          freshPolymorphicInstance InstanceQ True tySch coercions indices

      -- register any constraints of the data constructor into the solver
      otherTypeConstraints <- enforceConstraints s constraints
      registerWantedTypeConstraints otherTypeConstraints

      -- Running example:
      -- tySch      = S : forall {n.0 : Nat, t.10 : Nat, t.11 : Type} . N a.3 n.0 -> N t.11 t.10
      -- coercions = t.10 ~ n.0 + 1, t.11 ~ a.3
      -- 1 is an index position

      -- <REPORT>
      reportM $ "Matching on constructor " <> pretty dataC <> "\n"
      reportM $ "Type scheme  = " <> pretty tySch
      reportM $ "Coercions    = " <> pretty coercions
      reportM $ "Type indices = " <> pretty indices
      reportMsep
      reportM $ "Freshe freshTyVarsCtxt = " <> pretty freshTyVarsCtxt

      reportM $ "Freshened type scheme = " <> pretty dataConstructorTypeFresh
      reportM $ "Freshened coercions   = " <> pretty coercions'
      -- </REPORT>

      -- dataConstructorTypeFresh = N a.3.0 n.0.0 -> N t.11.0 t.10.0
      -- freshTyVarSubst = a.3 ~> a.3.0, n.0 ~> n.0.0, t.10 ~> t.10.0, t.11 ~ t.11.0 [TODO: WRONG WAY ROUND!?]
      -- coercions' = t.9.0 ~ n.0.0 + 1, t.11.0 ~ a.3.0

      -- TODO: Maybe remove
--      dataConstructorTypeFresh <- substitute (flipSubstitution coercions') dataConstructorTypeFresh

      -- dataConstructorTypeFresh = N t.11.0 n.0.0 -> N t.11.0 t.10.0

      st <- get
      reportMsep
      reportM $ "Computing equality " <> prettyNested (resultType dataConstructorTypeFresh) <> " == " <> prettyNested ty
      reportM $ " (under type variable context = " <> pretty (tyVarContext st) <> ")"

      -- Equality between N t.11.0 t.10.0 ~ N a`2 n`1
      -- where a`2 and n`1 are \forall quantified

      areEq <- equalTypesRelatedCoeffectsAndUnify s Eq PatternCtxt (resultType dataConstructorTypeFresh) ty
      debugM "Patterns.ctxtFromTypedPattern areEq" $ show areEq
      case areEq of
        (True, ty, unifiers) -> do

          -- Put in the ty var context any foralls bound here in the pattern
          -- unifying them with the data constructor's equality information
          freshTyVarsCtxt' <- substitute unifiers freshTyVarsCtxt

          let before = tyVarBindsRequested
          reportM $ "freshTyVarsCtxt' = " <> pretty freshTyVarsCtxt
          reportM $ "tyVarBinders = " <> (pretty tyVarBinders)
          let after = (take (length tyVarBindsRequested) freshTyVarsCtxt')
          reportM $ "requested variables were " <> pretty tyVarBindsRequested
          reportM $ "corresponds to " <> pretty after
          -- create a substitution for this variable
          let bodySubst = map (\(id_b, (id_a, _)) -> (id_b, SubstT $ TyVar id_a)) (zip before after)
          reportM $ "substitution due to implicits is " <> pretty bodySubst
          --let explicitBinds = map (\(id, ty) -> (id, (ty, ForallQ))) after
          -- modify (\st -> st { tyVarContext = explicitBinds ++ tyVarContext st })



          reportM $ "EQUAL with unifiers " <> pretty unifiers
          -- Predicate now says:
          --    t.10.0 ~ n.0.0 + 1
          --    t.11.0 ~ a.3.0
          -- Register coercions as equalities
          --mapM_ (\(var, SubstT t) ->
          --             equalTypesRelatedCoeffectsAndUnify s Eq PatternCtxt (TyVar var) t) coercions'

          -- unifiers:   t.10.0 ~ n`1
          --             t.11.0 ~ a`2
          st <- get
          reportM $ "Predicate stack" <> (pretty $ predicateStack st)

          dataConstructorIndexRewritten <- substitute unifiers dataConstructorTypeFresh

          -- dataConstructorFresh          = N t.11.0 n.0.0 -> N t.11.0 t.10.0
          -- dataConstructorIndexRewritten = N a`2 n.0.0 -> N a`2 n`1

          dataConstructorIndexRewrittenAndSpecialised <- substitute coercions' dataConstructorIndexRewritten
          reportM $ "Remaining type for the pattern constructor after equality unifiers and freshened coercions are applied: " <> pretty dataConstructorIndexRewrittenAndSpecialised

          -- dataConstructorIndexRewrittenAndSpecialised = N a`2 n.0.0 -> N a`2 n`1

          -- Debugging
          debugM "ctxt" $ "\n\t### unifiers = " <> pretty unifiers <> "\n"
                        <> "\n\t### drewrit = " <> pretty dataConstructorIndexRewritten
                        <> "\n\t### drewritAndSpec = " <> pretty dataConstructorIndexRewrittenAndSpecialised <> "\n"

          reportM $ "Rescursive checking of pattern typing on patterns (" <> pretty ps <> ") at (to be decomposed) types " <> prettyNested dataConstructorIndexRewrittenAndSpecialised

          -- Recursively apply pattern matching on the internal patterns to the constructor pattern
          (bindingContexts, _, bs, us, elabPs, consumptionsOut) <-
            ctxtFromTypedPatterns' outerBoxTy s pos dataConstructorIndexRewrittenAndSpecialised ps (replicate (length ps) cons)
          let consumptionOut = foldr meetConsumption Full consumptionsOut

          reportMsep
          reportM $ "Recursive check of patterns resulted in unification: " <> pretty us

          -- TODO: GO BACK TO THIS
          -- Apply the coercions to the type
          -- (`ty` used for working out definition unification)
          debugM "### pattern" (pretty ty)
          ty <- substitute coercions' ty
          debugM "### pattern" (pretty ty)

          -- Unifiers are only those things that include index variables

          -- unifiers:   t.10.0 ~ n`1


          -- let unifiers' = filter (\(id, subst) -> case lookup id (tyVarContext st) of Just (_, BoundQ) -> True; _ -> False) unifiers
          --debugM "ctxt" $ "unifiers': " <> show unifiers'

          -- Combine the substitutions
          --     n`1 ~ t.10.0
          -- subst <- combineSubstitutions s (flipSubstitution unifiers') us
          subst <- combineManySubstitutions s [unifiers, us, coercions', bodySubst]
          debugM "ctxt" $ "\n\t### outSubst = " <> pretty subst <> "\n"
          reportM $ "Output substitution = " <> pretty subst

          -- ### outSubst = n`1 ~ n.0.0 + 1
          --                t.11.0 ~ a.3.0
          --                t.10.0 ~ n.0.0 + 1

          definiteUnification s pos outerBoxTy ty
          -- (ctxtSubbed, ctxtUnsubbed) <- substCtxt subst as

          let elabP = PConstr s ty rf dataC tyVarBindsRequested elabPs

          -- Level tracking
          -- GHOST variable made from coeff added to assumptions
          ghostCtxt <-
                case outerBoxTy of
                  Nothing -> do
                    -- Linear context so return ghost used as 1
                    debugM "ctxtFromTypedPattern no ghost" $ "ty: " <> show ty <> "\t" <> pretty ty <> "\nPConstr: " <> pretty dataC
                    return usedGhostVariableContext
                  Just (coeff, _) -> do
                    isLevely <- isLevelKinded s coeff
                    debugM "ctxtFromTypedPattern outerBoxTy" $ "ty: " <> pretty outerBoxTy <> "\n" <> pretty (Ghost coeff) <> "\n" <> "isLevely: " <> show isLevely
                    if SecurityLevels `elem` globalsExtensions ?globals
                    then return [(mkId ghostName, Ghost coeff) | isLevely] -- [(mkId ".var.ghost.pattern", Ghost defaultGhost)]
                    else return []


          debugM "context in ctxtFromTypedPattern' PConstr" $ show (bindingContexts <> ghostCtxt)

          -- Apply context converge # of all the inner binding contexts and the local ghost context here
          outputContext <- ghostVariableContextMeet (bindingContexts <> ghostCtxt)

          return (outputContext, -- ctxtSubbed <> ctxtUnsubbed,     -- concatenate the contexts
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

ctxtFromTypedPattern' _ s _ t p _ = do
  st <- get
  debugM "ctxtFromTypedPattern" $ "Type: " <> show t <> "\nPat: " <> show p
  debugM "dataConstructors in checker state" $ show $ dataConstructors st
  case t of
    (Star _ t') -> throw $ UniquenessError { errLoc = s, uniquenessMismatch = UniquePromotion t'}
    _ -> throw PatternTypingError { errLoc = s, errPat = p, tyExpected = t }

flattenCoeffects :: (?globals :: Globals) => Span -> Maybe (Coeffect, Type) -> Maybe (Coeffect, Type) -> Checker (Maybe (Coeffect, Type), Substitution)
flattenCoeffects s Nothing Nothing | usingExtension GradedBase = do
  one <- generatePolymorphicGrade1 s
  return (Just one, [])

flattenCoeffects _ Nothing r = return (r, [])
flattenCoeffects _ r Nothing = return (r, [])
flattenCoeffects s (Just (outerCoeff, outerCoeffTy)) (Just (innerCoeff, innerCoeffTy)) = do
  flatM <- flattenable outerCoeffTy innerCoeffTy
  case flatM of
    Just (flattenOp, subst, ty) -> return (Just (flattenOp outerCoeff innerCoeff, ty), subst)
    Nothing -> throw DisallowedCoeffectNesting
      { errLoc = s, errTyOuter = outerCoeffTy, errTyInner = innerCoeffTy }



{-

  `ctxtFromTypedPatterns pp ty ps consumption`
  Parameters
    - pp = the position in which the pattern is occuring
    - ty = the types of the inputs and the output (e.g. in the form of a FunTy)
    - ps = a list of patterns
    - consumption = consumption information (DEPRECATED)

  Returns a tuples of a:
    - binding context
    - type for the body (with any specialisations applied)
    - any type variables which have been bound
    - an outgoing substitution [TODO: is this needed for the predicate in case we need to update any info?]
    - the type-elaborated patterns
    - consumption information (DEPRECATED)

-}
ctxtFromTypedPatterns :: (?globals :: Globals)
  => Span
  -> PatternPosition
  -> Type
  -> [Pattern ()]
  -> [Consumption]
  -> Checker (Ctxt Assumption, Type, Ctxt Kind, Substitution, [Pattern Type], [Consumption])
ctxtFromTypedPatterns = ctxtFromTypedPatterns' Nothing

ctxtFromTypedPatterns' :: (?globals :: Globals)
  => Maybe (Coeffect, Type)
  -> Span
  -> PatternPosition
  -> Type
  -> [Pattern ()]
  -> [Consumption]
  -> Checker (Ctxt Assumption, Type, Ctxt Kind, Substitution, [Pattern Type], [Consumption])
ctxtFromTypedPatterns' _ sp _ ty [] _ =
  return ([], ty, [], [], [], [])

ctxtFromTypedPatterns' outerCoeff s pos (FunTy _ grade t1 t2) (pat:pats) (cons:consumptionsIn) = do

  -- Match a pattern
  -- Flatten outerCoeff (if there is one) with the grade here
  (gradeWithTy, subst0a) <- case grade of
                              Nothing -> return (Nothing, [])
                              Just r  -> do
                                (gradeTy, substGradeTy, _) <- synthKind s r
                                return (Just (r, gradeTy), substGradeTy)
  (innerCoeff, subst0b) <- flattenCoeffects s outerCoeff gradeWithTy

  (localGam, eVars, subst, elabP, consumption) <- ctxtFromTypedPattern' innerCoeff s pos t1 pat cons

  -- Apply substitution to the outgoing type
  t2' <- substitute subst t2

  -- Match the rest
  (localGam', ty, eVars', substs, elabPs, consumptions) <-
      ctxtFromTypedPatterns' outerCoeff s pos (normaliseType t2') pats consumptionsIn

  -- Combine the results
  substs' <- combineManySubstitutions s [subst0a, subst0b, subst, substs]
  -- TODO: probably you can make the first part of this component be calculated more efficiently
  newLocalGam <- ghostVariableContextMeet $ localGam <> localGam'
  return (newLocalGam, ty, eVars ++ eVars', substs', elabP : elabPs, consumption : consumptions)

ctxtFromTypedPatterns' _ s _ ty (p:ps) _ = do
  -- This means we have patterns left over, but the type is not a
  -- function type, so we need to throw a type error

  -- First build a representation of what the type would look like
  -- if this was well typed, i.e., if we have two patterns left we get
  -- p0 -> p1 -> ?
  psTyVars <- mapM (\_ -> freshIdentifierBase "?" Data.Functor.<&> (TyVar . mkId)) ps
  let spuriousType = foldr (FunTy Nothing Nothing) (TyVar $ mkId "?") psTyVars
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
      (\_ _ _ _ _ bss -> concat bss)
