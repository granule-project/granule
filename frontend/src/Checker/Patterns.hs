{-# LANGUAGE ImplicitParams #-}

module Checker.Patterns where

import Control.Monad.Trans.Maybe
import Control.Monad.State.Strict

import Checker.Types (equalTypesRelatedCoeffectsAndUnify, SpecIndicator(..))
import Checker.Coeffects
import Checker.Exhaustivity
import Checker.Monad
import Checker.Predicates
import Checker.Kinds
import Checker.Substitutions
import Context
import Syntax.Identifiers
import Syntax.Pattern
import Syntax.Type
import Syntax.Span
import Syntax.Pretty
import Utils
--import Data.Maybe (mapMaybe)

definitelyUnifying :: Pattern t -> Bool
definitelyUnifying (PConstr _ _ _ _) = True
definitelyUnifying (PInt _ _ _) = True
definitelyUnifying _ = False

-- | Given a pattern and its type, construct Just of the binding context
--   for that pattern, or Nothing if the pattern is not well typed
--   Returns also a list of any variables bound by the pattern
--   (e.g. for dependent matching) and a substitution for variables
--   caused by pattern matching (e.g., from unification).
ctxtFromTypedPattern :: (?globals :: Globals, Show t) => Span -> Type -> Pattern t
  -> MaybeT Checker (Ctxt Assumption, [Id], Substitution)

-- Pattern matching on wild cards and variables (linear)
ctxtFromTypedPattern _ t (PWild _ _) = do
    -- Fresh variable to represent this (linear) value
    --   Wildcards are allowed, but only inside boxed patterns
    --   The following binding context will become discharged
    wild <- freshVar "wild"
    return ([(Id "_" wild, Linear t)], [], [])

ctxtFromTypedPattern _ t (PVar _ _ v) =
    return ([(v, Linear t)], [], [])

-- Pattern matching on constarints
ctxtFromTypedPattern _ t@(TyCon c) (PInt _ _ _)
  | internalName c == "Int" = return ([], [], [])

ctxtFromTypedPattern _ t@(TyCon c) (PFloat _ _ _)
  | internalName c == "Float" = return ([], [], [])

-- Pattern match on a modal box
ctxtFromTypedPattern s (Box coeff ty) (PBox _ _ p) = do
    (ctx, eVars, subst) <- ctxtFromTypedPattern s ty p
    k <- inferCoeffectType s coeff

    -- Check whether a unification was caused
    when (definitelyUnifying p)
        $ addConstraintToPreviousFrame $ ApproximatedBy s (COne k) coeff k

    -- Discharge all variables bound by the inner pattern
    return (map (discharge k coeff) ctx, eVars, subst)

ctxtFromTypedPattern _ ty p@(PConstr s _ dataC ps) = do
  debugM "Patterns.ctxtFromTypedPattern" $ "ty: " <> show ty <> "\t" <> pretty ty <> "\nPConstr: " <> pretty dataC

  st <- get
  case lookup dataC (dataConstructors st) of
    Nothing ->
      halt $ UnboundVariableError (Just s) $
             "Data constructor `" <> pretty dataC <> "`" <?> show (dataConstructors st)
    Just tySch -> do
      (dataConstructorTypeFresh, freshTyVars) <- freshPolymorphicInstance BoundQ tySch

      debugM "Patterns.ctxtFromTypedPattern" $ pretty dataConstructorTypeFresh <> "\n" <> pretty ty
      areEq <- equalTypesRelatedCoeffectsAndUnify s Eq True PatternCtxt (resultType dataConstructorTypeFresh) ty
      case areEq of
        (True, _, unifiers) -> do
          dataConstrutorSpecialised <- substitute unifiers dataConstructorTypeFresh
          (t,(as, bs, us)) <- unpeel ps dataConstrutorSpecialised
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
          return (ctxtSubbed <> ctxtUnsubbed, freshTyVars<>bs, subst)

        _ -> halt $ PatternTypingError (Just s) $
                  "Expected type `" <> pretty ty <> "` but got `" <> pretty dataConstructorTypeFresh <> "`"
  where
    unpeel :: Show t => [Pattern t] -> Type -> MaybeT Checker (Type, ([(Id, Assumption)], [Id], Substitution))
    unpeel = unpeel' ([],[],[])
    unpeel' acc [] t = return (t,acc)
    unpeel' (as,bs,us) (p:ps) (FunTy t t') = do
        (as',bs',us') <- ctxtFromTypedPattern s t p
        us <- combineSubstitutions s us us'
        unpeel' (as<>as',bs<>bs',us) ps t'
    unpeel' _ (p:_) t = halt $ PatternTypingError (Just s) $
              "Have you applied constructor `" <> sourceName dataC <>
              "` to too many arguments?"

ctxtFromTypedPattern s t@(TyVar v) p = do
  case p of
    PVar _ _ x -> return ([(x, Linear t)], [], [])
    PWild _ _  -> return ([], [], [])
    p          -> halt $ PatternTypingError (Just s)
                   $  "Cannot unify pattern " <> pretty p
                   <> "with type variable " <> pretty v

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

ctxtFromTypedPatterns ::
  (?globals :: Globals, Show t) => Span -> Type -> [Pattern t] -> MaybeT Checker (Ctxt Assumption, Type)
ctxtFromTypedPatterns sp ty [] = do
  debugM "Patterns.ctxtFromTypedPatterns" $ "Called with span: " <> show sp <> "\ntype: " <> show ty
  return ([], ty)
ctxtFromTypedPatterns s (FunTy t1 t2) (pat:pats) = do
  -- TODO: when we have dependent matching at the function clause
  -- level, we will need to pay attention to the bound variables here
  (localGam, _, _) <- ctxtFromTypedPattern s t1 pat
  pIrrefutable <- isIrrefutable s t1 pat
  if pIrrefutable then do
    (localGam', ty) <- ctxtFromTypedPatterns s t2 pats
    return (localGam <> localGam', ty)
  else refutablePattern s pat

ctxtFromTypedPatterns s ty ps = do
  -- This means we have patterns left over, but the type is not a
  -- function type, so we need to throw a type error

  -- First build a representation of what the type would look like
  -- if this was well typed, i.e., if we have two patterns left we get
  -- p0 -> p1 -> ?
  psTyVars <- mapM (\_ -> freshVar "?" >>= return . TyVar . mkId) ps
  let spuriousType = foldr FunTy (TyVar $ mkId "?") psTyVars
  halt $ GenericError (Just s)
     $ "Too many patterns.\n   Therefore, couldn't match expected type '"
       <> pretty ty
       <> "'\n   against a type of the form '" <> pretty spuriousType
       <> "' implied by the remaining patterns"
