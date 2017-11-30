{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Checker.Types where

import Syntax.Expr
import Syntax.Pretty
import Context
import Data.List

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

import Checker.Coeffects
import Checker.Constraints
import Checker.Monad
import Checker.Kinds

-- | Given a pattern and its type, construct Just of the binding context
--   for that pattern, or Nothing if the pattern is not well typed
ctxtFromTypedPattern
   :: Bool -> Span -> Type -> Pattern -> MaybeT Checker (Maybe (Ctxt Assumption))

-- Pattern matching on wild cards and variables (linear)
ctxtFromTypedPattern _ _ t              (PWild _)      = do
    -- Fresh variable to represent this (linear) value
    --   Wildcards are allowed, but only inside boxed patterns
    --   The following binding context will become discharged
    wild <- freshVar "wild"
    return $ Just [(wild, Linear t)]

ctxtFromTypedPattern _ _ t              (PVar _ v)     = return $ Just [(v, Linear t)]

-- Pattern matching on constarints
ctxtFromTypedPattern _ _ (TyCon "Int")   (PInt _ _)     = return $ Just []
ctxtFromTypedPattern _ _ (TyCon "Float") (PFloat _ _)   = return $ Just []
ctxtFromTypedPattern _ _ (TyCon "Bool")  (PConstr _ "True")  = return $ Just []
ctxtFromTypedPattern _ _ (TyCon "Bool")  (PConstr _ "False") = return $ Just []

-- Pattern match on a modal box
ctxtFromTypedPattern dbg s (Box coeff ty) (PBox _ p) = do
    ctx <- ctxtFromTypedPattern dbg s ty p
    k <- inferCoeffectType s coeff
    case ctx of
      -- Discharge all variables bound by the inner pattern
      Just ctx' -> return . Just $ map (discharge k coeff) ctx'
      Nothing   -> return Nothing
  where
    discharge _ c (v, Linear t) = (v, Discharged t c)
    discharge k c (v, Discharged t c') =
      case flattenable k of
        -- Implicit flatten operation allowed on this coeffect
        Just flattenOp -> (v, Discharged t (flattenOp c c'))
        Nothing        -> (v, Discharged t c')

-- Match a Nil constructor
ctxtFromTypedPattern _ s (TyApp (TyApp (TyCon "List") n) _) (PConstr _ "Nil") = do
    let kind = CConstr "Nat="
    case n of
      TyVar v -> addConstraint $ Eq s (CVar v) (CNat Discrete 0) kind
      TyInt m -> addConstraint $ Eq s (CNat Discrete m) (CNat Discrete 0) kind
    return $ Just []

-- Match a Cons constructor
ctxtFromTypedPattern dbg s
    (TyApp  (TyApp  (TyCon "List") n) t)
    (PApp _ (PApp _ (PConstr _ "Cons") p1) p2) = do
    -- Create a fresh type variable for the size of the consed list
    let kind = CConstr "Nat="
    sizeVar <- freshCoeffectVar "in" kind

    -- Recursively construct the binding patterns
    bs1 <- ctxtFromTypedPattern dbg s t p1
    bs2 <- ctxtFromTypedPattern dbg s (TyApp (TyApp (TyCon "List") (TyVar sizeVar)) t) p2

    -- Generate equality constraint
    let sizeVarInc = CPlus (CVar sizeVar) (CNat Discrete 1)
    case n of
      TyVar v -> addConstraint $ Eq s (CVar v) sizeVarInc kind
      TyInt m -> addConstraint $ Eq s (CNat Discrete m) sizeVarInc kind

    -- Join the two pattern contexts together
    return $ bs1 >>= (\bs1' -> bs2 >>= (\bs2' -> Just (bs1' ++ bs2')))

ctxtFromTypedPattern dbg s (PairTy lty rty) (PPair _ lp rp) = do
  ctxtL <- ctxtFromTypedPattern dbg s lty lp
  ctxtR <- ctxtFromTypedPattern dbg s rty rp
  return $ ctxtL >>= (\ctxtL' -> ctxtR >>= (\ctxtR' -> Just (ctxtL' ++ ctxtR')))

ctxtFromTypedPattern _ _ _ _ = return Nothing -- TODO: Remove cath-all

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
  ctx <- ctxtFromTypedPattern dbg s t1 pat
  case ctx of
    Just localGam -> do
      (localGam', ty) <- ctxtFromTypedPatterns dbg s t2 pats
      return (localGam ++ localGam', ty)
    Nothing -> illTypedPattern s t1 pat



lEqualTypes :: Bool -> Span -> Type -> Type -> MaybeT Checker (Bool, Type)
lEqualTypes dbg s = equalTypesRelatedCoeffectsAndUnify dbg s Leq

equalTypes :: Bool -> Span -> Type -> Type -> MaybeT Checker (Bool, Type)
equalTypes dbg s = equalTypesRelatedCoeffectsAndUnify dbg s Eq

type Unifier = [(Id, Type)]

{- | Check whether two types are equal, and at the same time
     generate coeffect equality constraints and unify the
     two types

     The first argument is taken to be possibly approximated by the second
     e.g., the first argument is inferred, the second is a specification
     being checked against
-}
equalTypesRelatedCoeffectsAndUnify ::
      Bool
   -> Span
   -- Explain how coeffects should be related by a solver constraint
   -> (Span -> Coeffect -> Coeffect -> CKind -> Constraint)
   -> Type -> Type -> MaybeT Checker (Bool, Type)
equalTypesRelatedCoeffectsAndUnify dbg s rel t1 t2 = do
   (eq, unif) <- equalTypesRelatedCoeffects dbg s rel t1 t2
   if eq
     then return (eq, applyUnifier unif t1)
     else return (eq, t1)

{- | Check whether two types are equal, and at the same time
     generate coeffect equality constraints and a unifier

     The first argument is taken to be possibly approximated by the second
     e.g., the first argument is inferred, the second is a specification
     being checked against -}
equalTypesRelatedCoeffects ::
      Bool
   -> Span
   -- Explain how coeffects should be related by a solver constraint
   -> (Span -> Coeffect -> Coeffect -> CKind -> Constraint)
   -> Type -> Type -> MaybeT Checker (Bool, Unifier)
equalTypesRelatedCoeffects dbg s rel (FunTy t1 t2) (FunTy t1' t2') = do
  (eq1, u1) <- equalTypesRelatedCoeffects dbg s rel t1' t1 -- contravariance
  (eq2, u2) <- equalTypesRelatedCoeffects dbg s rel t2 t2' -- covariance
  return (eq1 && eq2, u1 ++ u2)

equalTypesRelatedCoeffects _ _ _ (TyCon con) (TyCon con') =
  return (con == con', [])

equalTypesRelatedCoeffects dbg s rel (Diamond ef t) (Diamond ef' t') = do
  (eq, unif) <- equalTypesRelatedCoeffects dbg s rel t t'
  if ef == ef'
    then return (eq, unif)
    else
      -- Effect approximation
      if (ef `isPrefixOf` ef')
      then return (eq, unif)
      else do
        illGraded s $ "Effect mismatch: " ++ pretty ef ++ " not equal to " ++ pretty ef'
        halt

equalTypesRelatedCoeffects dbg s rel (Box c t) (Box c' t') = do
  -- Debugging
  dbgMsg dbg $ pretty c ++ " == " ++ pretty c'
  dbgMsg dbg $ "[ " ++ show c ++ " , " ++ show c' ++ "]"
  -- Unify the coeffect kinds of the two coeffects
  kind <- mguCoeffectTypes s c c'
  addConstraint (rel s c c' kind)
  equalTypesRelatedCoeffects dbg s rel t t'

equalTypesRelatedCoeffects dbg s rel (TyApp t1 t2) (TyApp t1' t2') = do
  (one, u1) <- equalTypesRelatedCoeffects dbg s rel t1 t1'
  (two, u2) <- equalTypesRelatedCoeffects dbg s rel t2 t2'
  return (one && two, u1 ++ u2)

equalTypesRelatedCoeffects _ s _ (TyVar n) (TyInt m) = do
  addConstraint (Eq s (CVar n) (CNat Discrete m) (CConstr "Nat="))
  return (True, [(n, TyInt m)])

equalTypesRelatedCoeffects _ s _ (TyVar n) (TyVar m) | n == m = do
  checkerState <- get
  case lookup n (ckctxt checkerState) of
    Just _ -> return (True, [])
    Nothing -> unknownName s ("Type variable " ++ n ++ " is unbound.")

equalTypesRelatedCoeffects _ s _ (TyVar n) (TyVar m) = do
  checkerState <- get
  case (lookup n (ckctxt checkerState), lookup m (ckctxt checkerState)) of

    -- Two universally quantified variables are unequal
    (Just (_, ForallQ), Just (_, ForallQ)) ->
      return (False, [])

    -- We can unify two existential type variables
    (Just (KType, ExistsQ), Just (KType, ExistsQ)) ->
      return (True, [(n, TyVar m)])

    -- We can unify a forall to an existential
    (Just (KType, ForallQ), Just (KType, ExistsQ)) ->
        return (True, [(n, TyVar m)])

    (Just (KType, ExistsQ), Just (KType, ForallQ)) ->
        return (True, [(m, TyVar n)])

    -- Trying to unify other (existential) variables
    (Just (KType, _), Just (k, _)) | k /= KType -> do
      checkerState <- get
      k <- inferKindOfType s (stripQuantifiers $ ckctxt checkerState) (TyVar m)
      illKindedUnifyVar s (TyVar n) KType (TyVar m) k

    (Just (k, _), Just (KType, _)) | k /= KType -> do
      checkerState <- get
      k <- inferKindOfType s (stripQuantifiers $ ckctxt checkerState) (TyVar n)
      illKindedUnifyVar s (TyVar n) k (TyVar m) KType

    -- Otherwise
    x -> do
     addConstraint (Eq s (CVar n) (CVar m) (CConstr "Nat="))
     return (True, [])

equalTypesRelatedCoeffects dbg s rel (PairTy t1 t2) (PairTy t1' t2') = do
  (lefts, u1)  <- equalTypesRelatedCoeffects dbg s rel t1 t1'
  (rights, u2) <- equalTypesRelatedCoeffects dbg s rel t2 t2'
  return (lefts && rights, u1 ++ u2)

equalTypesRelatedCoeffects dbg s rel (TyVar n) t = do
  checkerState <- get
  k1 <- inferKindOfType s (stripQuantifiers $ ckctxt checkerState) (TyVar n)
  k2 <- inferKindOfType s (stripQuantifiers $ ckctxt checkerState) t
  if k1 == k2
    then return (True, [(n, t)])
    else illKindedUnifyVar s (TyVar n) k1 t k2

equalTypesRelatedCoeffects dbg s rel t (TyVar n) =
  equalTypesRelatedCoeffects dbg s rel (TyVar n) t

equalTypesRelatedCoeffects _ s _ t1 t2 =
  illTyped s $ "I don't know how to make '" ++ pretty t2 ++ "' and '" ++ pretty t1 ++ "' equal."

-- | rewrite a type using a unifier (map from type vars to types)
applyUnifier :: Unifier -> Type -> Type
applyUnifier unif (TyVar v) = do
    case lookup v unif of
      Just t  -> t
      Nothing -> TyVar v
applyUnifier unif (FunTy t1 t2) =
    FunTy (applyUnifier unif t1) (applyUnifier unif t2)
applyUnifier unif (TyCon t) = TyCon t
applyUnifier unif (Diamond e t) =
    Diamond e (applyUnifier unif t)
applyUnifier unif (Box c t) =
    Box c (applyUnifier unif t)
applyUnifier unif (TyApp t1 t2) =
    TyApp (applyUnifier unif t1) (applyUnifier unif t2)
applyUnifier unif (TyInt t) = TyInt t
applyUnifier unif (PairTy t1 t2) =
    PairTy (applyUnifier unif t1) (applyUnifier unif t2)

-- Essentially equality on types but join on any coeffects
joinTypes :: Bool -> Span -> Type -> Type -> MaybeT Checker Type
joinTypes dbg s (FunTy t1 t2) (FunTy t1' t2') = do
  t1j <- joinTypes dbg s t1' t1 -- contravariance
  t2j <- joinTypes dbg s t2 t2'
  return (FunTy t1j t2j)

joinTypes _ _ (TyCon t) (TyCon t') | t == t' = return (TyCon t)

joinTypes dbg s (Diamond ef t) (Diamond ef' t') = do
  tj <- joinTypes dbg s t t'
  if ef `isPrefixOf` ef'
    then return (Diamond ef' tj)
    else
      if ef' `isPrefixOf` ef
      then return (Diamond ef tj)
      else do
        illGraded s $ "Effect mismatch: " ++ pretty ef ++ " not equal to " ++ pretty ef'
        halt

joinTypes dbg s (Box c t) (Box c' t') = do
  kind <- mguCoeffectTypes s c c'
  -- Create a fresh coeffect variable
  topVar <- freshCoeffectVar "" kind
  -- Unify the two coeffects into one
  addConstraint (Leq s c  (CVar topVar) kind)
  addConstraint (Leq s c' (CVar topVar) kind)
  tu <- joinTypes dbg s t t'
  return $ Box (CVar topVar) tu


joinTypes _ _ (TyInt n) (TyInt m) | n == m = return $ TyInt n

joinTypes _ s (TyInt n) (TyVar m) = do
  -- Create a fresh coeffect variable
  let kind = CConstr "Nat="
  var <- freshCoeffectVar m kind
  -- Unify the two coeffects into one
  addConstraint (Eq s (CNat Discrete n) (CVar var) kind)
  return $ TyInt n

joinTypes dbg s (TyVar n) (TyInt m) = joinTypes dbg s (TyInt m) (TyVar n)

joinTypes _ s (TyVar n) (TyVar m) = do
  -- Create fresh variables for the two tyint variables
  let kind = CConstr "Nat="
  nvar <- freshCoeffectVar n kind
  mvar <- freshCoeffectVar m kind
  -- Unify the two variables into one
  addConstraint (Leq s (CVar nvar) (CVar mvar) kind)
  return $ TyVar n

joinTypes dbg s (TyApp t1 t2) (TyApp t1' t2') = do
  t1'' <- joinTypes dbg s t1 t1'
  t2'' <- joinTypes dbg s t2 t2'
  return (TyApp t1'' t2'')

joinTypes _ s t1 t2 =
  illTyped s
    $ "Type '" ++ pretty t1 ++ "' and '"
               ++ pretty t2 ++ "' have no upper bound"



instance Pretty (Type, Ctxt Assumption) where
    pretty (t, _) = pretty t

instance Pretty (Id, Assumption) where
    pretty (v, ty) = v ++ " : " ++ pretty ty

instance Pretty Assumption where
    pretty (Linear ty) = pretty ty
    pretty (Discharged ty c) = "|" ++ pretty ty ++ "|." ++ pretty c

instance Pretty (Ctxt TypeScheme) where
   pretty xs = "{" ++ intercalate "," (map pp xs) ++ "}"
     where pp (var, t) = var ++ " : " ++ pretty t

instance Pretty (Ctxt Assumption) where
   pretty xs = "{" ++ intercalate "," (map pp xs) ++ "}"
     where pp (var, Linear t) = var ++ " : " ++ pretty t
           pp (var, Discharged t c) = var ++ " : .[" ++ pretty t ++ "]. " ++ pretty c
