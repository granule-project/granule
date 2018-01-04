{-# LANGUAGE ImplicitParams #-}

module Checker.Patterns where

import Control.Monad.Trans.Maybe
import Control.Monad.State.Strict

import Checker.Types (equalTypes)
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
    return ([(wild, Linear t)], [], [])

ctxtFromTypedPattern _ t (PVar _ v) =
    return ([(v, Linear t)], [], [])

-- Pattern matching on constarints
ctxtFromTypedPattern _ t@(TyCon "Int")   (PInt _ _) =
    return ([], [], [])
ctxtFromTypedPattern _ t@(TyCon "Float") (PFloat _ _) =
    return ([], [], [])

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
ctxtFromTypedPattern s t@(TyApp (TyApp (TyCon "List") n) ty) (PConstr _ "Nil") = do
    let kind = CConstr "Nat="
    -- Create a fresh type variable for the size of the consed list
    sizeVar <- freshCoeffectVarWithBinding "in" kind BoundQ
    case n of
      TyVar v -> do
        addConstraint $ Eq s (CVar v) (CVar sizeVar) kind
        addConstraint $ Eq s (CVar sizeVar) (CNat Discrete 0) kind
        return ([], [sizeVar], [(v, TyInt 0)])
      TyInt m -> do
        addConstraint $ Eq s (CNat Discrete m) (CNat Discrete 0) kind
        return ([], [], [])
      _ -> unhandled

-- Match a Cons constructor
ctxtFromTypedPattern s
    (TyApp  (TyApp  (TyCon "List") n) ty)
    (PApp _ (PApp _ (PConstr _ "Cons") p1) p2) = do
    -- Create a fresh type variable for the size of the consed list
    let kind = CConstr "Nat="
    sizeVar <- freshCoeffectVarWithBinding "in" kind BoundQ

    -- Recursively construct the binding patterns
    (bs1, eVars1, ty') <- ctxtFromTypedPattern s ty p1
    (bs2, eVars2, _) <- ctxtFromTypedPattern s (TyApp (TyApp (TyCon "List") (TyVar sizeVar)) ty) p2

    -- Generate equality constraint
    let sizeVarInc = CPlus (CVar sizeVar) (CNat Discrete 1)
    subst <- case n of
      TyVar v -> do
         addConstraint $ Eq s (CVar v) sizeVarInc kind
         return $ [(v, TyInfix "+" (TyVar sizeVar) (TyInt 1))]
      TyInt m -> do
         addConstraint $ Eq s (CNat Discrete m) sizeVarInc kind
         return []
      _ -> unhandled

    -- Join the two pattern contexts together
    return (bs1 ++ bs2, sizeVar : eVars1 ++ eVars2, subst)

-- Match a Z constructor
ctxtFromTypedPattern s t@(TyApp (TyCon "N") n) (PConstr _ "Z") = do
    c <- compileNatKindedTypeToCoeffect s n
    addConstraint $ Eq s c (CNat Discrete 0) (CConstr "Nat=")
    case n of
      TyVar v -> return ([], [], [(v, TyInt 0)])
      _ -> return ([], [], [])
        {-do
        sizeVar <- freshCoeffectVarWithBinding "in" (CConstr "Nat=") BoundQ
        addConstraint $ Eq s c (CNat Discret 0) sizeVar
        return ([], [], [(v, sizeVar)])-}

-- Match a S constructor
ctxtFromTypedPattern s t@(TyApp (TyCon "N") n) (PApp _ (PConstr _ "S") p) = do
    -- Create a fresh type variable for the size of the consed list
    let kind = CConstr "Nat="
    sizeVar <- freshCoeffectVarWithBinding "in" kind BoundQ

    -- Recursively construct the binding patterns
    (bs2, eVars2, _) <- ctxtFromTypedPattern s (TyApp (TyCon "N") (TyVar sizeVar)) p

    -- Generate equality constraint
    let sizeVarInc = CPlus (CVar sizeVar) (CNat Discrete 1)
    subst <- case n of
      TyVar v -> do
         addConstraint $ Eq s (CVar v) sizeVarInc kind
         return $ [(v, TyInfix "+" (TyVar sizeVar) (TyInt 1))]
      TyInt m -> do
         addConstraint $ Eq s (CNat Discrete m) sizeVarInc kind
         return []
      _ -> unhandled

    -- Join the two pattern contexts together
    return (bs2, sizeVar : eVars2, subst)


ctxtFromTypedPattern s (PairTy lty rty) (PPair _ lp rp) = do
  (ctxtL, eVars1, substl) <- ctxtFromTypedPattern s lty lp
  (ctxtR, eVars2, substr) <- ctxtFromTypedPattern s rty rp
  return $ (ctxtL ++ ctxtR, eVars1 ++ eVars2, substl ++ substr)

-- ctxtFromTypedPattern _ _ t@(TyCon "Bool")  (PConstr _ "True") =
--     return ([], [], [])
-- ctxtFromTypedPattern _ _ t@(TyCon "Bool")  (PConstr _ "False") =
--     return ([], [], [])
ctxtFromTypedPattern _ ty (PConstr s dataC) = do
  st <- get
  case lookup dataC (dataConstructors st) of
    Nothing ->
      halt $ UnboundVariableError (Just s) $
             "Data constructor `" ++ pretty dataC ++ "`" <?> (dataConstructors st)

    Just tySch -> do
      t <- freshPolymorphicInstance tySch
      debugM "Patterns.ctxtFromTypedPattern" $ pretty t ++ pretty ty
      areEq <- equalTypes s t ty
      case areEq of
        (True, _, unifiers) -> return ([], [], unifiers)
        _ -> halt $ PatternTypingError (Just s) $
                  "Expected type `" ++ pretty ty ++ "` but got `" ++ pretty t ++ "`"

ctxtFromTypedPattern _ ty (PApp s p1 p2) = do
   (binders1, tyvars1, subst1, t1) <- synthTypedPattern p1 -- checking patterns
   case t1 of
     FunTy arg res -> do
       subst <- equalTypes s res ty
       case subst of
         (True, _, unifiers) -> do
           let arg' = substType unifiers arg
           (binders2, tyvars2, subst2) <- ctxtFromTypedPattern s arg' p2
           (binders, binders') <- substCtxt subst2 (binders1 ++ binders2)
           return (binders ++ binders', tyvars1 ++ tyvars2, [])

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

synthTypedPattern :: (?globals :: Globals) => Pattern
  -> MaybeT Checker (Ctxt Assumption, [Id], Ctxt Type, Type)
synthTypedPattern p = do
  case p of
    PVar s name -> halt $ PatternTypingError (Just s) $
                          "Expected a data constructor, but got `" ++ name ++ "`"
    PWild s -> halt $ PatternTypingError (Just s) $
                      "Expected a data constructor, but got a wildcard."
    PInt s _ -> return ([], [], [], TyCon "Int")
    PFloat s _ -> return ([], [], [], TyCon "Float")
    PConstr s name -> do
      st <- get
      case lookup name (dataConstructors st) of
        Nothing -> halt $ UnboundVariableError (Just s) $ "Constructor `" ++ name ++ "`"
        Just (Forall _ _ t) -> return ([], [], [], t)
    PApp s p1 p2 -> do
      (binders1, tyvars1, subst1, t1) <- synthTypedPattern p1
      case t1 of
        TyApp arg res -> do
          (binders2, tyvars2, subst2) <- ctxtFromTypedPattern s arg p2
          (binders, binders') <- substCtxt subst2 (binders1 ++ binders2)
          debugM "PApp******" $ show $ substType subst2 res
          return (binders ++ binders', tyvars1 ++ tyvars2, [], substType subst2 res)
        t -> halt $ PatternTypingError (Just s) $
                    "Expected function type but got `" ++ pretty t
                    ++ "` in pattern `" ++ pretty p1 ++ "`"
      -- need to look at substitutions that come from checking right apply on the return
    -- PPair _ p1 p2 -> do
    --   (binders1, tyvars1, subst1, t1) <- synthTypedPattern p1
    --   (binders2, tyvars2, subst2, t2) <- synthTypedPattern p2
    --   return (binders1 ++ binders2 {-?-}, tyvars1 ++ tyvars2, [{-?-}], PairTy t1 t2)

ctxtFromTypedPatterns ::
  (?globals :: Globals) => Span -> Type -> [Pattern] -> MaybeT Checker (Ctxt Assumption, Type)
ctxtFromTypedPatterns _ ty [] =
  return ([], ty)
ctxtFromTypedPatterns s (FunTy t1 t2) (pat:pats) = do
  -- TODO: when we have dependent matching at the function clause
  -- level, we will need to pay attention to the bound variables here
  (localGam, _, _) <- ctxtFromTypedPattern s t1 pat
  (localGam', ty) <- ctxtFromTypedPatterns s t2 pats
  return (localGam ++ localGam', ty)

ctxtFromTypedPatterns s ty p =
  error $ "Unhandled case: ctxtFromTypedPatterns called with:\
          \Span: " ++ show s ++ "\nType: " ++ show ty ++ "\nPatterns: " ++ show p
