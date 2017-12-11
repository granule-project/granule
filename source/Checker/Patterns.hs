module Checker.Patterns where

import Context
import Syntax.Expr
import Syntax.Pretty
import Checker.Monad
import Checker.Predicates
import Checker.Coeffects

import Control.Monad.Trans.Maybe

-- | Given a pattern and its type, construct Just of the binding context
--   for that pattern, or Nothing if the pattern is not well typed
--   Returns also a list of any variables bound by the pattern
--   (e.g. for dependent matching) and a substitution for variables
ctxtFromTypedPattern
   :: Bool
   -> Span
   -> Type
   -> Pattern
   -> MaybeT Checker (Ctxt Assumption, [Id], Ctxt Type)

-- Pattern matching on wild cards and variables (linear)
ctxtFromTypedPattern _ _ t (PWild _) = do
    -- Fresh variable to represent this (linear) value
    --   Wildcards are allowed, but only inside boxed patterns
    --   The following binding context will become discharged
    wild <- freshVar "wild"
    return ([(wild, Linear t)], [], [])

ctxtFromTypedPattern _ _ t (PVar _ v) =
    return ([(v, Linear t)], [], [])

-- Pattern matching on constarints
ctxtFromTypedPattern _ _ t@(TyCon "Int")   (PInt _ _) =
    return ([], [], [])
ctxtFromTypedPattern _ _ t@(TyCon "Float") (PFloat _ _) =
    return ([], [], [])
ctxtFromTypedPattern _ _ t@(TyCon "Bool")  (PConstr _ "True") =
    return ([], [], [])
ctxtFromTypedPattern _ _ t@(TyCon "Bool")  (PConstr _ "False") =
    return ([], [], [])

-- Pattern match on a modal box
ctxtFromTypedPattern dbg s (Box coeff ty) (PBox _ p) = do
    (ctx, eVars, subst) <- ctxtFromTypedPattern dbg s ty p
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
ctxtFromTypedPattern _ s t@(TyApp (TyApp (TyCon "List") n) ty) (PConstr _ "Nil") = do
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

-- Match a Cons constructor
ctxtFromTypedPattern dbg s
    t@(TyApp  (TyApp  (TyCon "List") n) ty)
    (PApp _ (PApp _ (PConstr _ "Cons") p1) p2) = do
    -- Create a fresh type variable for the size of the consed list
    let kind = CConstr "Nat="
    sizeVar <- freshCoeffectVarWithBinding "in" kind BoundQ

    -- Recursively construct the binding patterns
    (bs1, eVars1, ty') <- ctxtFromTypedPattern dbg s ty p1
    (bs2, eVars2, _) <- ctxtFromTypedPattern dbg s (TyApp (TyApp (TyCon "List") (TyVar sizeVar)) t) p2

    -- Generate equality constraint
    let sizeVarInc = CPlus (CVar sizeVar) (CNat Discrete 1)
    subst <- case n of
      TyVar v -> do
         addConstraint $ Eq s (CVar v) sizeVarInc kind
         return $ [(v, TyInfix "+" (TyVar sizeVar) (TyInt 1))]
      TyInt m -> do
         addConstraint $ Eq s (CNat Discrete m) sizeVarInc kind
         return []

    -- Join the two pattern contexts together
    return (bs1 ++ bs2, sizeVar : eVars1 ++ eVars2, subst)

-- Match a Nil constructor
ctxtFromTypedPattern _ s t@(TyApp (TyCon "N") n) (PConstr _ "Z") = do
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

-- Match a Cons constructor
ctxtFromTypedPattern dbg s t@(TyApp (TyCon "N") n) (PApp _ (PConstr _ "S") p) = do
    -- Create a fresh type variable for the size of the consed list
    let kind = CConstr "Nat="
    sizeVar <- freshCoeffectVarWithBinding "in" kind BoundQ

    -- Recursively construct the binding patterns
    (bs2, eVars2, _) <- ctxtFromTypedPattern dbg s (TyApp (TyCon "Nat") (TyVar sizeVar)) p

    -- Generate equality constraint
    let sizeVarInc = CPlus (CVar sizeVar) (CNat Discrete 1)
    subst <- case n of
      TyVar v -> do
         addConstraint $ Eq s (CVar v) sizeVarInc kind
         return $ [(v, TyInfix "+" (TyVar sizeVar) (TyInt 1))]
      TyInt m -> do
         addConstraint $ Eq s (CNat Discrete m) sizeVarInc kind
         return []

    -- Join the two pattern contexts together
    return (bs2, sizeVar : eVars2, subst)


ctxtFromTypedPattern dbg s (PairTy lty rty) (PPair _ lp rp) = do
  (ctxtL, eVars1, substl) <- ctxtFromTypedPattern dbg s lty lp
  (ctxtR, eVars2, substr) <- ctxtFromTypedPattern dbg s rty rp
  return $ (ctxtL ++ ctxtR, eVars1 ++ eVars2, substl ++ substr)

ctxtFromTypedPattern _ s t p =
  illTyped s
    $ "Pattern match " ++ pretty p ++ " does not have type " ++ pretty t

-- | Given a list of patterns and a (possible nested) function type
--   match the patterns against each argument, returning a binding context
--   as well as the remaining type.
--   e.g. given type A -> B -> C and patterns [Constr "A", Constr "B"] then
--     the remaining type is C.
ctxtFromTypedPatterns ::
  Bool -> Span -> Type -> [Pattern] -> MaybeT Checker (Ctxt Assumption, Type)
ctxtFromTypedPatterns _ _ ty [] =
  return ([], ty)
ctxtFromTypedPatterns dbg s (FunTy t1 t2) (pat:pats) = do
  -- TODO: when we have dependent matching at the function clause
  -- level, we will need to pay attention to the bound variables here
  (localGam, _, _) <- ctxtFromTypedPattern dbg s t1 pat
  (localGam', ty) <- ctxtFromTypedPatterns dbg s t2 pats
  return (localGam ++ localGam', ty)

ctxtFromTypedPatterns _ s ty p =
  error $ "Unhandled case: ctxtFromTypedPatterns called with:\
          \Span: " ++ show s ++ "\nType: " ++ show ty ++ "\nPatterns: " ++ show p

