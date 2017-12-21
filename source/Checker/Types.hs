{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Checker.Types where

import Syntax.Expr
import Syntax.Pretty
import Context
import Data.List
import Data.Functor.Identity

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

import Checker.Coeffects
import Checker.Constraints
import Checker.Monad
import Checker.Kinds
import Checker.Predicates
import Checker.Substitutions

lEqualTypes ::
    Bool -> Span -> Type -> Type -> MaybeT Checker (Bool, Type, Ctxt Type)
lEqualTypes dbg s = equalTypesRelatedCoeffectsAndUnify dbg s Leq

equalTypes ::
    Bool -> Span -> Type -> Type -> MaybeT Checker (Bool, Type, Ctxt Type)
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
   -> Type -> Type -> MaybeT Checker (Bool, Type, Ctxt Type)
equalTypesRelatedCoeffectsAndUnify dbg s rel t1 t2 = do
   (eq, unif) <- equalTypesRelatedCoeffects dbg s rel t1 t2
   if eq
     then return (eq, substType unif t1, unif)
     else return (eq, t1, [])

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
  -- contravariant position (always approximate)
  (eq1, u1) <- equalTypesRelatedCoeffects dbg s Leq t1' t1
   -- covariant position (depends is not always over approximated)
  (eq2, u2) <- equalTypesRelatedCoeffects dbg s rel t2 t2'
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

equalTypesRelatedCoeffects _ s _ (TyVar n) (TyVar m) | n == m = do
  checkerState <- get
  case lookup n (tyVarContext checkerState) of
    Just _ -> return (True, [])
    Nothing -> unknownName s ("Type variable " ++ n ++ " is unbound.")

equalTypesRelatedCoeffects _ s _ (TyVar n) (TyVar m) = do
  checkerState <- get

  case (lookup n (tyVarContext checkerState), lookup m (tyVarContext checkerState)) of

    -- Two universally quantified variables are unequal
    (Just (_, ForallQ), Just (_, ForallQ)) ->
      return (False, [])

    -- We can unift a universal a dependently bound universal
    (Just (k1, ForallQ), Just (k2, BoundQ)) ->
      tyVarConstraint k1 k2 n m

    (Just (k1, BoundQ), Just (k2, ForallQ)) ->
      tyVarConstraint k1 k2 n m

    -- We can unify two instance type variables
    (Just (k1, InstanceQ), Just (k2, InstanceQ)) ->
      tyVarConstraint k1 k2 n m

    -- But we can unify a forall and an instance
    (Just (KType, ForallQ), Just (KType, InstanceQ)) ->
      return (True, [(n, TyVar m)])
    (Just (KType, InstanceQ), Just (KType, ForallQ)) ->
      return (True, [(m, TyVar n)])

    -- Trying to unify other (existential) variables
    (Just (KType, _), Just (k, _)) | k /= KType -> do
      k <- inferKindOfType s (TyVar m)
      illKindedUnifyVar s (TyVar n) KType (TyVar m) k

    (Just (k, _), Just (KType, _)) | k /= KType -> do
      k <- inferKindOfType s (TyVar n)
      illKindedUnifyVar s (TyVar n) k (TyVar m) KType

    -- Otherwise
    (Just (k1, _), Just (k2, _)) ->
      tyVarConstraint k1 k2 n m

    (t1, t2) -> error $ show t1 ++ "\n" ++ show t2
  where
    tyVarConstraint k1 k2 n m = do
      case k1 `joinKind` k2 of
        Just (KConstr kc) -> do
          addConstraint (Eq s (CVar n) (CVar m) (CConstr kc))
          return (True, [(n, TyVar m)])
        Just _ ->
          return (True, [(n, TyVar m)])
        Nothing ->
          return (False, [])

equalTypesRelatedCoeffects dbg s rel (PairTy t1 t2) (PairTy t1' t2') = do
  (lefts, u1)  <- equalTypesRelatedCoeffects dbg s rel t1 t1'
  (rights, u2) <- equalTypesRelatedCoeffects dbg s rel t2 t2'
  return (lefts && rights, u1 ++ u2)

equalTypesRelatedCoeffects dbg s rel (TyVar n) t = do
  checkerState <- get
  case lookup n (tyVarContext checkerState) of
    -- We can unify an instance with a concrete type
    (Just (k1, q)) | q == InstanceQ || q == BoundQ -> do
      k2 <- inferKindOfType s t
      case k1 `joinKind` k2 of
        Nothing -> illKindedUnifyVar s (TyVar n) k1 t k2

        -- If the kind is Nat=, then create a solver constraint
        Just (KConstr "Nat=") -> do
          nat <- compileNatKindedTypeToCoeffect s t
          addConstraint (Eq s (CVar n) nat (CConstr "Nat="))
          return (True, [(n, t)])

        Just _ -> return (True, [(n, t)])

    -- But we can't unify an universal with a concrete type
    (Just (k1, ForallQ)) -> do
      ut <- unrenameType t
      illTyped s $ "Trying to unify a polymorphic type '" ++ n
       ++ "' with monomorphic " ++ pretty ut

    Nothing -> unknownName s n

equalTypesRelatedCoeffects dbg s rel t (TyVar n) =
  equalTypesRelatedCoeffects dbg s rel (TyVar n) t

equalTypesRelatedCoeffects _ s _ t1 t2 = do
  k1 <- inferKindOfType s t1
  k2 <- inferKindOfType s t2
  case (k1, k2) of
    (KConstr n, KConstr n') | "Nat" `isPrefixOf` n && "Nat" `isPrefixOf` n' -> do
       c1 <- compileNatKindedTypeToCoeffect s t1
       c2 <- compileNatKindedTypeToCoeffect s t2
       addConstraint $ Eq s c1 c2 (CConstr "Nat=")
       return (True, [])
    (KType, KType) -> do
        ut1 <- unrenameType t1
        ut2 <- unrenameType t2
        illTyped s $ pretty ut1 ++ " is not equal to " ++ pretty ut2

    _ -> do
       ut1 <- unrenameType t1
       ut2 <- unrenameType t2
       illTyped s $ "Equality is not defined between kinds "
                 ++ pretty k1 ++ " and " ++ pretty k2
                 ++ "\t\n from equality "
                 ++ "'" ++ pretty ut2 ++ "' and '" ++ pretty ut1 ++ "' equal."


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

joinTypes _ s t1 t2 = do
  ut1 <- unrenameType t1
  ut2 <- unrenameType t2
  illTyped s
    $ "Type '" ++ pretty ut1 ++ "' and '"
               ++ pretty ut2 ++ "' have no upper bound"