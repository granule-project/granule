{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Patterns where

import Control.Monad.Trans.Maybe
import Control.Monad.State.Strict
import Data.List (intercalate)

import Language.Granule.Checker.Errors
import Language.Granule.Checker.Types (equalTypesRelatedCoeffectsAndUnify, SpecIndicator(..))
import Language.Granule.Checker.Coeffects
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Substitutions
import Language.Granule.Checker.Variables

import Language.Granule.Context
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Pretty
import Language.Granule.Utils
--import Data.Maybe (mapMaybe)

definitelyUnifying :: Pattern t -> Bool
definitelyUnifying (PConstr _ _ _ _) = True
definitelyUnifying (PInt _ _ _) = True
definitelyUnifying _ = False

-- | Predicate on whether a type has more than 1 shape (constructor)
polyShaped :: (?globals :: Globals) => Type -> MaybeT Checker Bool
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
--      - a list of any variables bound by the pattern
--        (e.g. for dependent matching)
--      - a substitution for variables
--           caused by pattern matching (e.g., from unification),
--      - a consumption context explaining usage triggered by pattern matching
ctxtFromTypedPattern :: (?globals :: Globals, Show t) =>
  Span
  -> Type
  -> Pattern t
  -> Consumption   -- Consumption behaviour of the patterns in this position so far
  -> MaybeT Checker (Ctxt Assumption, [Id], Substitution, Pattern Type, Consumption)

-- Pattern matching on wild cards and variables (linear)
ctxtFromTypedPattern _ t (PWild s _) cons =
    case cons of
      Full ->
        -- Full consumption is allowed here
        return ([], [], [], PWild s t, Full)

      _ -> illLinearityMismatch s [NonLinearPattern]

ctxtFromTypedPattern _ t (PVar s _ v) _ = do
    let elabP = PVar s t v
    return ([(v, Linear t)], [], [], elabP, NotFull)

-- Pattern matching on constarints
ctxtFromTypedPattern _ t@(TyCon c) (PInt s _ n) _
  | internalName c == "Int" = do
    let elabP = PInt s t n
    return ([], [], [], elabP, Full)

ctxtFromTypedPattern _ t@(TyCon c) (PFloat s _ n) _
  | internalName c == "Float" = do
    let elabP = PFloat s t n
    return ([], [], [], elabP, Full)

-- Pattern match on a modal box
ctxtFromTypedPattern s t@(Box coeff ty) (PBox sp _ p) _ = do

    (ctx, eVars, subst, elabPinner, _) <- ctxtFromTypedPattern s ty p Full
    coeffTy <- inferCoeffectType s coeff

    -- Check whether a unification was caused
    isPoly <- polyShaped ty
    when (definitelyUnifying p && isPoly) $ do
      -- (addConstraintToPreviousFrame $ Neq s (CZero coeffTy) coeff coeffTy)
      --addConstraintToPreviousFrame $ Eq s (COne coeffTy) coeff coeffTy
      addConstraintToPreviousFrame $ ApproximatedBy s (COne coeffTy) coeff coeffTy


    --when (containsNoUnifyingUpToNextBox p) $ do
    --  addConstraintToPreviousFrame $ ApproximatedBy s (CZero coeffTy) coeff coeffTy

      --(addConstraintToPreviousFrame $ Neq s (CZero coeffTy) coeff coeffTy)
      --x <- freshIdentifierBase "x"
      --addConstraintToPreviousFrame $ NonZeroPromotableTo s (mkId x) coeff coeffTy

      -- An alternate idea to do with dummy/shadow vars
    {- ctxtUnificationCoeffect <-
        if definitelyUnifying p
        then do
          -- Create a dummy variable that is discharged (1) of type k
          v <- freshIdentifierBase "guardUnif"
          return [(mkId v, Discharged (TyCon $ mkId "()") (COne coeffTy))]
        else return [] -}

    {- Old approach
         -- addConstraintToPreviousFrame $ ApproximatedBy s (COne k) coeff k
        -- addConstraintToPreviousFrame $ Neq s (CZero k) coeff k
    -}

    let elabP = PBox sp t elabPinner

    -- Discharge all variables bound by the inner pattern
    ctxt' <- mapM (discharge s coeffTy coeff) ctx
    return (ctxt', eVars, subst, elabP, Full)

ctxtFromTypedPattern _ ty p@(PConstr s _ dataC ps) cons = do
  debugM "Patterns.ctxtFromTypedPattern" $ "ty: " <> show ty <> "\t" <> pretty ty <> "\nPConstr: " <> pretty dataC

  st <- get
  case lookup dataC (dataConstructors st) of
    Nothing ->
      halt $ UnboundVariableError (Just s) $
             "Data constructor `" <> pretty dataC <> "`" <?> show (dataConstructors st)
    Just tySch -> do
      (dataConstructorTypeFresh, freshTyVars) <-
          freshPolymorphicInstance BoundQ True tySch

      debugM "Patterns.ctxtFromTypedPattern" $ pretty dataConstructorTypeFresh <> "\n" <> pretty ty

      areEq <- equalTypesRelatedCoeffectsAndUnify s Eq True PatternCtxt (resultType dataConstructorTypeFresh) ty
      case areEq of
        (True, _, unifiers) -> do

          dataConstrutorSpecialised <- substitute unifiers dataConstructorTypeFresh

          (t,(as, bs, us, elabPs, consumptionOut)) <- unpeel ps dataConstrutorSpecialised
          subst <- combineSubstitutions s unifiers us
          (ctxtSubbed, ctxtUnsubbed) <- substCtxt subst as

          let elabP = PConstr s ty dataC elabPs
          return (ctxtSubbed <> ctxtUnsubbed, freshTyVars<>bs, subst, elabP, consumptionOut)

        _ -> halt $ PatternTypingError (Just s) $
                  "Expected type `" <> pretty ty <> "` but got `" <> pretty dataConstructorTypeFresh <> "`"
  where
    unpeel :: Show t
          -- A list of patterns for each part of a data constructor pattern
            => [Pattern t]
            -- The remaining type of the constructor
            -> Type
            -> MaybeT Checker (Type, ([(Id, Assumption)], [Id], Substitution, [Pattern Type], Consumption))
    unpeel = unpeel' ([],[],[],[],Full)

    -- Tail recursive version of unpell
    unpeel' acc [] t = return (t,acc)

    unpeel' (as,bs,us,elabPs,consOut) (p:ps) (FunTy t t') = do
        (as',bs',us',elabP, consOut') <- ctxtFromTypedPattern s t p cons
        us <- combineSubstitutions s us us'
        unpeel' (as<>as', bs<>bs', us, elabP:elabPs, consOut `meetConsumption` consOut') ps t'

    unpeel' _ (p:_) t = halt $ PatternTypingError (Just s) $
              "Have you applied constructor `" <> sourceName dataC <>
              "` to too many arguments?"


ctxtFromTypedPattern s t p _ = do
  st <- get
  debugM "ctxtFromTypedPattern" $ "Type: " <> show t <> "\nPat: " <> show p
  debugM "dataConstructors in checker state" $ show $ dataConstructors st
  halt $ PatternTypingError (Just s)
    $ "Pattern match `" <> pretty p <> "` does not match expected type `" <> pretty t <> "`"

discharge _ _ c (v, Linear t) = return (v, Discharged t c)
discharge s ct c (v, Discharged t c') = do
  ct' <- inferCoeffectType s c'
  return $ case flattenable ct ct' of
    -- Implicit flatten operation allowed on this coeffect
    Just (flattenOp, ct'')  -> (v, Discharged t (flattenOp c c'))
    Nothing                 -> (v, Discharged t c')

ctxtFromTypedPatterns :: (?globals :: Globals, Show t)
  => Span
  -> Type
  -> [Pattern t]
  -> [Consumption]
  -> MaybeT Checker (Ctxt Assumption, Type, [Id], Substitution, [Pattern Type], [Consumption])
ctxtFromTypedPatterns sp ty [] _ = do
  debugM "Patterns.ctxtFromTypedPatterns" $ "Called with span: " <> show sp <> "\ntype: " <> show ty
  return ([], ty, [], [], [], [])

ctxtFromTypedPatterns s (FunTy t1 t2) (pat:pats) (cons:consumptionsIn) = do
  -- TODO: when we have dependent matching at the function clause
  -- level, we will need to pay attention to the bound variables here
  (localGam, eVars, subst, elabP, consumption) <- ctxtFromTypedPattern s t1 pat cons

  (localGam', ty, eVars', substs, elabPs, consumptions) <-
      ctxtFromTypedPatterns s t2 pats consumptionsIn

  substs' <- combineSubstitutions s subst substs
  return (localGam <> localGam', ty, eVars ++ eVars', substs', elabP : elabPs, consumption : consumptions)

ctxtFromTypedPatterns s ty ps _ = do
  -- This means we have patterns left over, but the type is not a
  -- function type, so we need to throw a type error

  -- First build a representation of what the type would look like
  -- if this was well typed, i.e., if we have two patterns left we get
  -- p0 -> p1 -> ?
  psTyVars <- mapM (\_ -> freshIdentifierBase "?" >>= return . TyVar . mkId) ps
  let spuriousType = foldr FunTy (TyVar $ mkId "?") psTyVars
  halt $ GenericError (Just s)
     $ "Too many patterns.\n   Therefore, couldn't match expected type '"
       <> pretty ty
       <> "'\n   against a type of the form '" <> pretty spuriousType
       <> "' implied by the remaining patterns"

duplicateBinderCheck :: (?globals::Globals) => Span -> [Pattern a] -> MaybeT Checker ()
duplicateBinderCheck s ps = unless (null duplicateBinders) $
    halt $ DuplicatePatternError (Just s) $ intercalate ", " duplicateBinders
  where
    duplicateBinders = duplicates . concatMap getBinders $ ps
    getBinders = patternFold
      (\_ _ id -> [sourceName id])
      (\_ _ -> [])
      (\_ _ bs -> bs)
      (\_ _ _ -> [])
      (\_ _ _ -> [])
      (\_ _ _ bss -> concat bss)
