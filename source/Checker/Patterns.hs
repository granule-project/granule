{-# LANGUAGE ImplicitParams #-}

module Checker.Patterns where

import Control.Monad.Trans.Maybe
import Control.Monad.State.Strict

import Checker.Types (equalTypesWithUniversalSpecialisation, combineUnifiers)
import Checker.Coeffects
import Checker.Monad
import Checker.Predicates
import Checker.Substitutions
import Context
import Syntax.Expr
import Syntax.Pretty
import Utils


-- | Given a pattern and its type, construct Just of the binding context
--   for that pattern, or Nothing if the pattern is not well typed
--   Returns also a list of any variables bound by the pattern
--   (e.g. for dependent matching) and a substitution for variables
--   caused by pattern matching (e.g., from unification).
ctxtFromTypedPattern :: (?globals :: Globals ) => Span -> Type -> Pattern
  -> MaybeT Checker (Ctxt Assumption, [Id], Ctxt Type)

-- Pattern matching on wild cards and variables (linear)
ctxtFromTypedPattern _ t (PWild _) = do
    -- Fresh variable to represent this (linear) value
    --   Wildcards are allowed, but only inside boxed patterns
    --   The following binding context will become discharged
    wild <- freshVar "wild"
    return ([(mkInternalId "_" wild, Linear t)], [], [])

ctxtFromTypedPattern _ t (PVar _ v) =
    return ([(v, Linear t)], [], [])

-- Pattern matching on constarints
ctxtFromTypedPattern _ t@(TyCon c) (PInt _ _)
  | internalName c == "Int" = return ([], [], [])

ctxtFromTypedPattern _ t@(TyCon c) (PFloat _ _)
  | internalName c == "Float" = return ([], [], [])

-- Pattern match on a modal box
ctxtFromTypedPattern s (Box coeff ty) (PBox _ p) = do
    (ctx, eVars, subst) <- ctxtFromTypedPattern s ty p
    k <- inferCoeffectType s coeff
    -- Discharge all variables bound by the inner pattern
    return (map (discharge k coeff) ctx, eVars, subst)

  where
    discharge _ c (v, Linear t) = (v, Discharged t c)
    discharge k c (v, Discharged t c') =
      case flattenable k of
        -- Implicit flatten operation allowed on this coeffect
        Just flattenOp -> (v, Discharged t (flattenOp c c'))
        Nothing        -> (v, Discharged t c')

ctxtFromTypedPattern s (PairTy lty rty) (PPair _ lp rp) = do
  (ctxtL, eVars1, substl) <- ctxtFromTypedPattern s lty lp
  (ctxtR, eVars2, substr) <- ctxtFromTypedPattern s rty rp
  unifiers <- combineUnifiers s substl substr
  return (ctxtL ++ ctxtR, eVars1 ++ eVars2, unifiers)

ctxtFromTypedPattern _ ty (PConstr s dataC ps) = do
  debugM "Patterns.ctxtFromTypedPattern" $ "ty: " ++ show ty ++ "\t" ++ pretty ty ++ "\nPConstr: " ++ pretty dataC

  st <- get
  case lookup dataC (dataConstructors st) of
    Nothing ->
      halt $ UnboundVariableError (Just s) $
             "Data constructor `" ++ pretty dataC ++ "`" <?> show (dataConstructors st)
    Just tySch -> do
      (t,freshTyVars) <- freshPolymorphicInstance BoundQ tySch
      debugM "Patterns.ctxtFromTypedPattern" $ pretty t ++ "\n" ++ pretty ty

      -- unpeel `ty` by matching each pattern with the head of an arrow
      let unpeel = unpeel' ([],[],[])
          unpeel' acc [] t = return (t,acc)
          unpeel' (as,bs,us) (p:ps) (FunTy t t') = do
              (as',bs',us') <- ctxtFromTypedPattern s t p
              us <- combineUnifiers s us us'
              unpeel' (as++as',bs++bs',us) ps t'
          unpeel' _ (p:_) t = halt $ PatternTypingError (Just s) $
                    "Have you applied constructor `" ++ sourceName dataC ++
                    "` to too many arguments?"
      (t,(as,bs,us)) <- unpeel ps t
      areEq <- equalTypesWithUniversalSpecialisation s t ty
      case areEq of
        (True, _, unifiers) -> do
          us <- combineUnifiers s unifiers us
          return (as, freshTyVars++bs, us)

        _ -> halt $ PatternTypingError (Just s) $
                  "Expected type `" ++ pretty ty ++ "` but got `" ++ pretty t ++ "`"

ctxtFromTypedPattern s t@(TyVar v) p = do
  case p of
    PVar _ x -> return ([(x, Linear t)], [], [])
    PBox _ p' -> do
      polyName <- freshVar "k"
      cvar <- freshCoeffectVarWithBinding (mkId "c")  (CPoly $ mkId polyName) InstanceQ
      let c' = CVar cvar
      ty <- freshVar "t"
      let t' = TyVar $ mkId ty
      (binders, vars, unifiers) <- ctxtFromTypedPattern s t' p'
      return (binders, vars, (v, Box c' t') : unifiers)

ctxtFromTypedPattern s t p = do
  st <- get
  debugM "ctxtFromTypedPattern" $ "Type: " ++ show t ++ "\nPat: " ++ show p
  debugM "dataConstructors in checker state" $ show $ dataConstructors st
  halt $ PatternTypingError (Just s)
    $ "Pattern match `" ++ pretty p ++ "` does not have type `" ++ pretty t ++ "`"

ctxtFromTypedPatterns ::
  (?globals :: Globals) => Span -> Type -> [Pattern] -> MaybeT Checker (Ctxt Assumption, Type)
ctxtFromTypedPatterns sp ty [] = do
  debugM "Patterns.ctxtFromTypedPatterns" $ "Called with span: " ++ show sp ++ "\ntype: " ++ show ty
  return ([], ty)
ctxtFromTypedPatterns s (FunTy t1 t2) (pat:pats) = do
  -- TODO: when we have dependent matching at the function clause
  -- level, we will need to pay attention to the bound variables here
  (localGam, _, _) <- ctxtFromTypedPattern s t1 pat
  pIrrefutable <- isIrrefutable s t1 pat
  if pIrrefutable then do
    (localGam', ty) <- ctxtFromTypedPatterns s t2 pats
    return (localGam ++ localGam', ty)
  else refutablePattern s pat

ctxtFromTypedPatterns s ty p =
  error $ "Unhandled case: ctxtFromTypedPatterns called with:\
          \Span: " ++ show s ++ "\nType: " ++ show ty ++ "\nPatterns: " ++ show p

-- Calculates whether a given pattern match will always succeed
isIrrefutable ::
  (?globals :: Globals ) => Span -> Type -> Pattern -> MaybeT Checker Bool
isIrrefutable s t (PVar _ _) = return True
isIrrefutable s t (PWild _)  = return True
isIrrefutable s (PairTy t1 t2) (PPair _ p1 p2) = do
    g1 <- isIrrefutable s t1 p1
    g2 <- isIrrefutable s t2 p2
    return (g1 && g2)
isIrrefutable s (Box _ t) (PBox _ p) =
  isIrrefutable s t p
-- TODO: data types with only one constructor can have
-- irrefutable patterns... but we need and easier way to index
-- the data constructors by what type they belong to
-- isIrrefutable s t (PConstr s id) =
isIrrefutable s (TyCon con) (PConstr _ pcon _ps)
   | internalName pcon == "()" && internalName con == "()" =
   return True
isIrrefutable s _ _ = return False
