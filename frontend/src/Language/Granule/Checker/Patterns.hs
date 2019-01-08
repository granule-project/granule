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

-- | Given a pattern and its type, construct Just of the binding context
--   for that pattern, or Nothing if the pattern is not well typed
--   Returns also:
--      - a list of any variables bound by the pattern
--        (e.g. for dependent matching)
--      - a substitution for variables
--           caused by pattern matching (e.g., from unification),
--      - a consumption context explaining usage triggered by pattern matching
ctxtFromTypedPattern :: (?globals :: Globals, Show t) => Span -> Type -> Pattern t
  -> MaybeT Checker (Ctxt Assumption, [Id], Substitution, Pattern Type)

-- Pattern matching on wild cards and variables (linear)
ctxtFromTypedPattern _ t (PWild s _) = do
    -- Fresh variable to represent this (linear) value
    --   Wildcards are allowed, but only inside boxed patterns
    --   The following binding context will become discharged
    wild <- freshIdentifierBase "wild"
    let elabP = PWild s t
    return ([(Id "_" wild, Linear t)], [], [], elabP)
    -- return ([], [], [], elabP)


ctxtFromTypedPattern _ t (PVar s _ v) = do
    let elabP = PVar s t v
    return ([(v, Linear t)], [], [], elabP)

-- Pattern matching on constarints
ctxtFromTypedPattern _ t@(TyCon c) (PInt s _ n)
  | internalName c == "Int" = do
    let elabP = PInt s t n
    return ([], [], [], elabP)

ctxtFromTypedPattern _ t@(TyCon c) (PFloat s _ n)
  | internalName c == "Float" = do
    let elabP = PFloat s t n
    return ([], [], [], elabP)

-- Pattern match on a modal box
ctxtFromTypedPattern s t@(Box coeff ty) (PBox sp _ p) = do

    (ctx, eVars, subst, elabPinner) <- ctxtFromTypedPattern s ty p
    coeffTy <- inferCoeffectType s coeff

    -- Check whether a unification was caused
    when (definitelyUnifying p) $ do
      (addConstraintToPreviousFrame $ Neq s (CZero coeffTy) coeff coeffTy)
      --addConstraintToPreviousFrame $ ApproximatedBy s (COne coeffTy) coeff coeffTy

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
    return (map (discharge coeffTy coeff) ctx, eVars, subst, elabP)

ctxtFromTypedPattern _ ty p@(PConstr s _ dataC ps) = do
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
          (t,(as, bs, us, elabPs)) <- unpeel ps dataConstrutorSpecialised
          subst <- combineSubstitutions s unifiers us
          (ctxtSubbed, ctxtUnsubbed) <- substCtxt subst as
          -- Updated type variable context
          {- state <- get
          tyVars <- mapM (\(v, (k, q)) -> do
                      k <- substitute subst k
                      return (v, (k, q))) (tyVarContext state)
          let kindSubst = mapMaybe (\(v, s) -> case s of
                                                SubstK k -> Just (v, k)
                                                _        -> Nothing) subst
          put (state { tyVarContext = tyVars
                    , kVarContext = kindSubst <> kVarContext state }) -}
          let elabP = PConstr s ty dataC elabPs
          return (ctxtSubbed <> ctxtUnsubbed, freshTyVars<>bs, subst, elabP)

        _ -> halt $ PatternTypingError (Just s) $
                  "Expected type `" <> pretty ty <> "` but got `" <> pretty dataConstructorTypeFresh <> "`"
  where
    unpeel :: Show t => [Pattern t] -> Type -> MaybeT Checker (Type, ([(Id, Assumption)], [Id], Substitution, [Pattern Type]))
    unpeel = unpeel' ([],[],[],[])
    unpeel' acc [] t = return (t,acc)
    unpeel' (as,bs,us,elabPs) (p:ps) (FunTy t t') = do
        (as',bs',us',elabP) <- ctxtFromTypedPattern s t p
        us <- combineSubstitutions s us us'
        unpeel' (as<>as',bs<>bs',us,elabP:elabPs) ps t'
    unpeel' _ (p:_) t = halt $ PatternTypingError (Just s) $
              "Have you applied constructor `" <> sourceName dataC <>
              "` to too many arguments?"

ctxtFromTypedPattern s t@(TyVar v) p = do
  case p of
    PVar s _ x -> do
      let elabP = PVar s t x
      return ([(x, Linear t)], [], [], elabP)

    PWild s _  -> do
      let elabP = PWild s t
      return ([], [], [], elabP)

    p          -> halt $ PatternTypingError (Just s)
                   $  "Cannot unify pattern `" <> pretty p
                   <> "` with type `" <> pretty v <> ""

ctxtFromTypedPattern s t p = do
  st <- get
  debugM "ctxtFromTypedPattern" $ "Type: " <> show t <> "\nPat: " <> show p
  debugM "dataConstructors in checker state" $ show $ dataConstructors st
  halt $ PatternTypingError (Just s)
    $ "Pattern match `" <> pretty p <> "` does not have type `" <> pretty t <> "`"

discharge _ c (v, Linear t) = (v, Discharged t c)
discharge k c (v, Discharged t c') =
  case flattenable k of
    -- Implicit flatten operation allowed on this coeffect
    Just flattenOp -> (v, Discharged t (flattenOp c c'))
    Nothing        -> (v, Discharged t c')

ctxtFromTypedPatterns :: (?globals :: Globals, Show t)
  => Span
  -> Type
  -> [Pattern t]
  -> MaybeT Checker (Ctxt Assumption, Type, [Id], Substitution, [Pattern Type])
ctxtFromTypedPatterns sp ty [] = do
  debugM "Patterns.ctxtFromTypedPatterns" $ "Called with span: " <> show sp <> "\ntype: " <> show ty
  return ([], ty, [], [], [])

ctxtFromTypedPatterns s (FunTy t1 t2) (pat:pats) = do
  -- TODO: when we have dependent matching at the function clause
  -- level, we will need to pay attention to the bound variables here
  (localGam, eVars, subst, elabP) <- ctxtFromTypedPattern s t1 pat

  (localGam', ty, eVars', substs, elabPs) <- ctxtFromTypedPatterns s t2 pats
  substs' <- combineSubstitutions s subst substs
  return (localGam <> localGam', ty, eVars ++ eVars', substs', elabP : elabPs)

ctxtFromTypedPatterns s ty ps = do
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
