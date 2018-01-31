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

-- Match a Nil constructor
ctxtFromTypedPattern s (TyApp (TyApp (TyCon listC) n) ty) (PConstr _ nilC)
  | internalName listC == "List" && internalName nilC == "Nil" = do
    let kind = CConstr $ mkId "Nat="
    c <- compileNatKindedTypeToCoeffect s n
    addConstraint $ Eq s c (CNat Discrete 0) kind
    case n of
      TyVar v -> return ([], [], [(v, TyInt 0)])
      _       -> return ([], [], [])

-- Match a Cons constructor
ctxtFromTypedPattern s (TyApp  (TyApp  (TyCon listC) n) ty) (PApp _ (PApp _ (PConstr _ consC) p1) p2)
  | internalName listC == "List" && internalName consC == "Cons" = do
    -- Create a fresh type variable for the size of the consed list
    let kind = CConstr $ mkId "Nat="
    sizeVar <- freshCoeffectVarWithBinding (mkId "in") kind BoundQ

    -- Recursively construct the binding patterns
    (bs1, eVars1, u1) <- ctxtFromTypedPattern s ty p1
    (bs2, eVars2, u2) <- ctxtFromTypedPattern s (TyApp (TyApp (TyCon $ mkId "List") (TyVar sizeVar)) ty) p2
    unifiers <- combineUnifiers s u1 u2

    -- Generate equality constraint
    let sizeVarInc = CPlus (CVar sizeVar) (CNat Discrete 1)
    c <- compileNatKindedTypeToCoeffect s n
    addConstraint $ Eq s c sizeVarInc kind

    -- Compute additional substitution
    -- TODO: this should be subsumed/generalised by the rest of
    -- type equality mechanism but isn't yet for some reason
    let u0 = case n of
          TyVar v -> [(v, TyInfix "+" (TyVar sizeVar) (TyInt 1))]
          _       -> []
    unifiers <- combineUnifiers s u0 unifiers
    -- Join the two pattern contexts together
    return (bs1 ++ bs2, sizeVar : eVars1 ++ eVars2, unifiers)

-- Match a Z constructor
ctxtFromTypedPattern s t@(TyApp (TyCon nC) n) (PConstr _ zC)
  | internalName nC == "N" && internalName zC == "Z" = do
    c <- compileNatKindedTypeToCoeffect s n
    addConstraint $ Eq s c (CNat Discrete 0) (CConstr $ mkId "Nat=")
    case n of
      TyVar v -> return ([], [], [(v, TyInt 0)])
      _       -> return ([], [], [])

-- Match a S constructor
ctxtFromTypedPattern s t@(TyApp (TyCon nC) n) (PApp _ (PConstr _ sC) p)
  | internalName nC == "N" && internalName sC == "S" = do
    -- Create a fresh type variable for the size of the consed list
    let kind = CConstr $ mkId "Nat="
    sizeVar <- freshCoeffectVarWithBinding (mkId "in") kind BoundQ

    -- Recursively construct the binding patterns
    (bs2, eVars2, u) <- ctxtFromTypedPattern s (TyApp (TyCon $ mkId "N") (TyVar sizeVar)) p

    -- Generate equality constraint
    let sizeVarInc = CPlus (CVar sizeVar) (CNat Discrete 1)
    c <- compileNatKindedTypeToCoeffect s n
    addConstraint $ Eq s c sizeVarInc kind

    -- Compute additional substitution
    -- TODO: this should be subsumed/generalised by the rest of
    -- type equality mechanism but isn't yet for some reason
    let u0 = case n of
          TyVar v -> [(v, TyInfix "+" (TyVar sizeVar) (TyInt 1))]
          _       -> []
    unifiers <- combineUnifiers s u u0
    -- Join the two pattern contexts together
    return (bs2, sizeVar : eVars2, unifiers)

ctxtFromTypedPattern s (PairTy lty rty) (PPair _ lp rp) = do
  (ctxtL, eVars1, substl) <- ctxtFromTypedPattern s lty lp
  (ctxtR, eVars2, substr) <- ctxtFromTypedPattern s rty rp
  unifiers <- combineUnifiers s substl substr
  return (ctxtL ++ ctxtR, eVars1 ++ eVars2, unifiers)

ctxtFromTypedPattern _ ty (PConstr s dataC) = do
  debugM "Patterns.ctxtFromTypedPattern" $ "ty: " ++ show ty ++ "\t" ++ pretty ty ++ "\nPConstr: " ++ pretty dataC
  st <- get
  case lookup dataC (dataConstructors st) of
    Nothing ->
      halt $ UnboundVariableError (Just s) $
             "Data constructor `" ++ pretty dataC ++ "`" <?> show (dataConstructors st)

    Just tySch -> do
      t <- freshPolymorphicInstance tySch
      debugM "Patterns.ctxtFromTypedPattern" $ pretty t ++ pretty ty
      areEq <- equalTypesWithUniversalSpecialisation s t ty
      case areEq of
        (True, _, unifiers) -> return ([], [], unifiers)
        _ -> halt $ PatternTypingError (Just s) $
                  "Expected type `" ++ pretty ty ++ "` but got `" ++ pretty t ++ "`"

ctxtFromTypedPattern _ ty (PApp s p1 p2) = do
   (binders1, tyvars1, subst1, t1) <- synthPatternTypeForPAppLeft p1 -- checking patterns
   case t1 of
     FunTy arg res -> do
       subst <- equalTypesWithUniversalSpecialisation s res ty
       case subst of
         (True, _, unifiers) -> do
           unifiers <- combineUnifiers s unifiers subst1
           let arg' = substType unifiers arg
           (binders2, tyvars2, subst2) <- ctxtFromTypedPattern s arg' p2
           unifiers <- combineUnifiers s unifiers subst2
           (binders, binders') <- substCtxt subst2 (binders1 ++ binders2)
           return (binders ++ binders', tyvars1 ++ tyvars2, unifiers)

         _ -> halt $ PatternTypingError (Just s) $
                    "Expected type `" ++ pretty ty ++ "` but got `" ++ pretty res ++ "`"


ctxtFromTypedPattern s t p = do
  st <- get
  debugM "ctxtFromTypedPattern" $ "Type: " ++ show t ++ "\nPat: " ++ show p
  debugM "dataConstructors in checker state" $ show $ dataConstructors st
  halt $ PatternTypingError (Just s)
    $ "Pattern match `" ++ pretty p ++ "` does not have type `" ++ pretty t ++ "`"

-- | Given a list of patterns and a (possible nested) function type
--   match the patterns against each argument, returning a binding context
--   as well as the remaining type.
--   e.g. given type A -> B -> C and patterns [Constr "A", Constr "B"] then
--     the remaining type is C.

synthPatternTypeForPAppLeft :: (?globals :: Globals) => Pattern
  -> MaybeT Checker (Ctxt Assumption, [Id], Ctxt Type, Type)
synthPatternTypeForPAppLeft p = do
  case p of
    PConstr s name -> do
      st <- get
      case lookup name (dataConstructors st) of
        Nothing -> halt $ UnboundVariableError (Just s) $ "Constructor `" ++ pretty name ++ "`"
        Just tySch -> do
          t <- freshPolymorphicInstance tySch
          return ([], [], [], t)
    PApp s p1 p2 -> do
      (binders1, tyvars1, subst1, t1) <- synthPatternTypeForPAppLeft p1
      case t1 of
        FunTy arg res -> do
          (binders2, tyvars2, subst2) <- ctxtFromTypedPattern s arg p2
          (binders, binders') <- substCtxt subst2 (binders1 ++ binders2)
          debugM "PApp" $ show $ substType subst2 res
          return (binders ++ binders', tyvars1 ++ tyvars2, [], substType subst2 res)
        t -> halt $ PatternTypingError (Just s) $
                    "Expected function type but got `" ++ pretty t
                    ++ "` in pattern `" ++ pretty p1 ++ "`"
    PVar s name -> halt $ PatternTypingError (Just s) $
                          "Expected a constructor pattern, but got `" ++ pretty name ++ "`"
    PWild s -> halt $ PatternTypingError (Just s) $
                      "Expected a constructor pattern, but got a wildcard"
    PInt s _ -> halt $ PatternTypingError (Just s) $
                      "Expected a constructor pattern, but got an `Int`"
    PFloat s _ -> halt $ PatternTypingError (Just s) $
                      "Expected a constructor pattern, but got a `Float`"
    pair@(PPair s _ _) -> halt $ PatternTypingError (Just s) $
                      "Expected a constructor pattern, but got `" ++ pretty pair ++ "`"

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
-- isIrrefutable s (PConstr s id) t =
isIrrefutable s _ _ = return False
