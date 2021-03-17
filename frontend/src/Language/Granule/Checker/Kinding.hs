{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Kind checking and inference algorithms
module Language.Granule.Checker.Kinding where

import Control.Arrow (second)
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Data.Maybe (fromMaybe)

import Language.Granule.Context

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Checker.Effects (effectTop, effectUpperBound)
import Language.Granule.Checker.Flatten (mguCoeffectTypes, Injections)
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Primitives
    (closedOperation, coeffectResourceAlgebraOps, tyOps)
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.Variables
--import Language.Granule.Checker.Normalise

import Language.Granule.Utils

-- | Check the kind of a definition
-- Currently we expec t that a type scheme has kind ktype
kindCheckDef :: (?globals :: Globals) => Def v t -> Checker (Def v t)
kindCheckDef (Def s id rf eqs (Forall s' quantifiedVariables constraints ty)) = do
  let localTyVarContext = universify quantifiedVariables

  -- Set up the quantified variables in the type variable context
  modify (\st -> st { tyVarContext = localTyVarContext })
  forM_ constraints $ \constraint -> checkKind s constraint kpredicate

  ty <- replaceSynonyms ty
  (unifiers, tyElaborated) <- checkKind s ty ktype

  -- Rewrite the quantified variables with their possibly updated kinds (inferred)
  qVars <- mapM (\(v, a) -> substitute unifiers a >>= (\b -> return (v, b))) quantifiedVariables
  modify (\st -> st { tyVarContext = [] })

  -- Update the def with the resolved quantifications
  return (Def s id rf eqs (Forall s' qVars constraints tyElaborated))

-- Replace any constructor IDs with their top-element
-- (i.e., IO gets replaces with the set of all effects as an alias)
replaceSynonyms :: Type -> Checker Type
replaceSynonyms ty =
    typeFoldM (baseTypeFold { tfTyCon = conCase }) ty
  where
    conCase conId = do
      let tyConId = TyCon conId
      effTop <- effectTop tyConId
      return $ fromMaybe tyConId effTop

------------------------------------------------------------

-- `checkKind s gam t k` checks with `gam |- t :: k` is derivable
-- and also returns an elaborated type term `t'` in the case that
-- some extra information is learned (e.g., resolving types of coeffect terms)
checkKind :: (?globals :: Globals) =>
  Span -> Type -> Kind -> Checker (Substitution, Type)

-- Avoid weird "type in type" style invocations.
checkKind s t k | t == k = do
  throw $ KindError s t k

-- KChk_funk
checkKind s (FunTy name t1 t2) k = do
  (subst1, t1') <- checkKind s t1 k
  (subst2, t2') <- checkKind s t2 k
  substFinal <- combineSubstitutions s subst1 subst2
  return (substFinal, FunTy name t1 t2)

-- KChk_SetKind
checkKind s (TyApp (TyCon (internalName -> "Set")) t) (TyCon (internalName -> "Coeffect")) =
  -- Sets as coeffects can be themselves over a coeffect type or some other type
  (checkKind s t kcoeffect) <|> (checkKind s t ktype)

checkKind s (TyApp (TyCon (internalName -> "Set")) t) (TyCon (internalName -> "Effect")) =
  -- Sets as effects can be themselves over an effect type or some other type
  (checkKind s t keffect) <|> (checkKind s t ktype)

checkKind s (TyApp (TyCon (internalName -> "SetOp")) t) (TyCon (internalName -> "Coeffect")) =
  -- Sets as coeffects can be themselves over a coeffect type or some other type
  (checkKind s t kcoeffect) <|> (checkKind s t ktype)

checkKind s (TyApp (TyCon (internalName -> "SetOp")) t) (TyCon (internalName -> "Effect")) =
  -- Sets as effects can be themselves over an effect type or some other type
  (checkKind s t keffect) <|> (checkKind s t ktype)

-- KChk_app
checkKind s (TyApp t1 t2) k2 = do
  (k1, subst1, t2') <- synthKind s t2
  (subst2, t1') <- checkKind s t1 (FunTy Nothing k1 k2)
  substFinal <- combineSubstitutions s subst1 subst2
  return (substFinal, TyApp t1' t2')

-- KChk_opRing and KChk_effOp combined (i.e. closed operators)
checkKind s t@(TyInfix op t1 t2) k | closedOperation op = do
  maybeSubst <- closedOperatorAtKind s op k
  case maybeSubst of
    Just subst3 -> do
      (subst1, t1') <- checkKind s t1 k
      (subst2, t2') <- checkKind s t2 k
      substFinal <- combineManySubstitutions s [subst1, subst2, subst3]
      return (substFinal, TyInfix op t1' t2')
    Nothing -> throw OperatorUndefinedForKind { errLoc = s, errTyOp = op, errK = k }

-- KChk_nat
checkKind s t@(TyInt n) k =
  case k of
    -- n : Nat
    TyCon (internalName -> "Nat") -> return ([], t)
    -- n : Q
    TyCon (internalName -> "Q") -> return ([], t)
    -- n : Ext Nat
    TyApp (TyCon (internalName -> "Ext")) (TyCon (internalName -> "Nat")) -> return ([], t)
    -- n : Interval k  (then we turn this into [n..n])
    TyApp (TyCon (internalName -> "Interval")) k' -> do
      (subst, k'') <- checkKind s t k'
      return (subst, TyInfix TyOpInterval t t)
    -- Not valid
    _ -> throw $ NaturalNumberAtWrongKind s t k

-- KChk_effOne
checkKind s t@(TyGrade mk n) k = do
  let k' = fromMaybe k mk
  jK <- maybe (return (Just (k, [], Nothing))) (\k' -> joinTypes s k' k) mk
  case jK of
    Just (k, subst, _) ->
      case n of
        0 -> do -- Can only be a semiring element
          (subst', _) <- checkKind s k kcoeffect
          substFinal <- combineSubstitutions s subst subst'
          return (substFinal, TyGrade (Just k) n)
        1 -> do -- Can be a monoid or semiring element
          (subst', _) <- (checkKind s k kcoeffect) <|> (checkKind s k keffect)
          substFinal <- combineSubstitutions s subst subst'
          return (substFinal, TyGrade (Just k) n)
        _ -> do -- Can only be a semiring element formed by repeated 1 + ...
          (subst', _) <- checkKind s k kcoeffect
          substFinal <- combineSubstitutions s subst subst'
          return (substFinal, TyGrade (Just k) n)
    Nothing ->
      throw $ UnificationError s k k'

-- KChk_set
checkKind s t@(TySet p elems) (TyApp (TyCon setConstructor) elemTy)
  | internalName setConstructor == "Set" || internalName setConstructor == "SetOp" = do
    case elems of
      [] -> return ([], t)
      _ -> do
        results <- mapM (\elem -> checkKind s elem elemTy) elems
        let (substs, elems') = unzip results
        substFinal <- combineManySubstitutions s substs
        return (substFinal, TySet p elems')

-- KChk_sig
checkKind s (TySig t k) k' = do
  join <- joinTypes s k k'
  case join of
    Just (jk, subst, inj) ->
      case inj of
        Nothing           -> return (subst, TySig t jk)
        -- Apply the left injection
        Just (inj1, inj2) -> return (subst, TySig (inj1 t) jk)
    Nothing -> throw KindMismatch { errLoc = s, tyActualK = Just t, kExpected = k, kActual = k' }

-- KChck_Nat
-- "Nat" belonds to Coeffect, Effect, and Type kinds
checkKind s t@(TyCon (internalName -> "Nat")) (TyCon (internalName -> "Coeffect")) =
  return ([], t)
checkKind s t@(TyCon (internalName -> "Nat")) (TyCon (internalName -> "Effect")) =
  return ([], t)
checkKind s t@(TyCon (internalName -> "Nat")) (Type 0) =
  return ([], t)

-- Fall through to synthesis if checking can not be done.
checkKind s t k = do
  -- Synth
  (k', subst1, t') <- synthKind s t
  -- See if we can do a join (equality+) on the synthed kind and the one coming as specification here.
  join <- joinTypes s k k'
  case join of
    Just (_, subst2, _) -> do
      substFinal <- combineSubstitutions s subst1 subst2
      return (substFinal, t')
    Nothing -> throw KindMismatch { errLoc = s, tyActualK = Just t, kExpected = k, kActual = k' }

------------------------------------------------------------

-- Given `synthKind gam t` it synthesis a `k` such that `gam |- t :: k` and
-- returns a substitution and an elebaroted type `t'` along with it.
synthKind :: (?globals :: Globals) =>
  Span -> Type -> Checker (Kind, Substitution, Type)
synthKind s t = synthKind' s (not (containsTypeSig t)) t

synthKind' :: (?globals :: Globals) =>
     Span
  -> Bool  -- Special flag: True means we can treat TyGrade as a Nat because there are no signatures
  -> Type
  -> Checker (Kind, Substitution, Type)

-- KChkS_var and KChkS_instVar
synthKind' s overloadToNat t@(TyVar x) = do
  st <- get
  case lookup x (tyVarContext st) of
    Just (k, _) -> return (k, [], t)
    Nothing     -> throw UnboundTypeVariable { errLoc = s, errId = x }


-- -- KChkS_fun
--
--      t1 => k    t2 <= k
--   ----------------------- Fun
--        t1 -> t2 => k

synthKind' s overloadToNat (FunTy name t1 t2) = do
  (k, subst1, t1') <- synthKind' s overloadToNat t1
  (subst2   , t2') <- checkKind s t2 k
  subst <- combineSubstitutions s subst1 subst2
  return (k, subst, FunTy name t1' t2')

-- KChkS_pair
synthKind' s overloadToNat (TyApp (TyApp (TyCon (internalName -> ",,")) t1) t2) = do
  (k1, subst1, t1') <- synthKind' s overloadToNat t1
  (k2, subst2, t2') <- synthKind' s overloadToNat t2
  subst <- combineSubstitutions s subst1 subst2
  return (TyApp (TyApp (TyCon $ mkId ",,") k1) k2, subst, TyApp (TyApp (TyCon $ mkId ",,") t1') t2')

-- KChkS_SetKind
synthKind' s overloadToNat (TyApp (TyCon (internalName -> "Set")) t) = do
  (k, subst, t') <- synthKind' s overloadToNat t
  case k of
    -- For set over type, default to the kind being Effect
    Type 0 -> return (keffect, subst, TyApp (TyCon (mkId "Set")) t')
    -- otherwise kind of the set depends on the kind of the elements
    k      -> return (k, subst, TyApp (TyCon (mkId "Set")) t')

-- KChkS_app
--
--      t1 => k1 -> k2    t2 <= k1
--   ------------------------------ Fun
--        t1 t2 => k
--
synthKind' s overloadToNat (TyApp t1 t2) = do
  (funK, subst1, t1') <- synthKind' s overloadToNat t1
  case funK of
    (FunTy _ k1 k2) -> do
      (subst2, t2') <- checkKind s t2 k1
      subst <- combineSubstitutions s subst1 subst2
      return (k2, subst, TyApp t1' t2')
    _ -> throw KindError { errLoc = s, errTy = t1, errKL = funK }

-- KChkS_interval
--
--      t1 => k1        t2 => k2     k1 ~ k2 =  k3
--   ----------------------------------------------- interval
--        t1 .. t2 => Interval k3
--
synthKind' s overloadToNat (TyInfix TyOpInterval t1 t2) = do
  (coeffTy1, subst1, t1') <- synthKind' s overloadToNat t1
  (coeffTy2, subst2, t2') <- synthKind' s overloadToNat t2
  (jcoeffTy, subst3, (inj1, inj2)) <- mguCoeffectTypes s coeffTy1 coeffTy2
  subst <- combineManySubstitutions s [subst1, subst2, subst3]
  -- Apply injections in the elaborated term
  return (TyApp (tyCon "Interval") jcoeffTy, subst, TyInfix TyOpInterval (inj1 t1') (inj2 t2'))

-- KChkS_predOp
synthKind' s overloadToNat t@(TyInfix op t1 t2) =
  synthForOperator s overloadToNat op t1 t2

-- KChkS_int
synthKind' s _ t@(TyInt n) = do
  return (TyCon (Id "Nat" "Nat"), [], t)

-- KChkS_grade [overload to Nat]
synthKind' s overloadToNat t@(TyGrade Nothing n) | overloadToNat =
  return (tyCon "Nat", [], TyInt n)

-- KChkS_grade [don't overload to Nat]
synthKind' s overloadToNat t@(TyGrade (Just k) n) =
  return (k, [], t)

-- KChkS_grade [don't overload to Nat]
synthKind' s overloadToNat t@(TyGrade Nothing n) | not overloadToNat = do
  -- TODO: is it problematic that we choose a semiring (coeffect)-kinded type
  -- rather than an effect one?
  var <- freshTyVarInContext (mkId $ "semiring[" <> pretty (startPos s) <> "]") kcoeffect
  return (TyVar var, [], t)

-- KChkS_box
synthKind' s _ (Box c t) = do
  -- Deal with the grade term
  (coeffTy, subst0, c') <- synthKind' s (not (containsTypeSig c)) c
  (subst1, _) <- checkKind s coeffTy kcoeffect
  -- Then the inner type
  (subst2, t') <- checkKind s t ktype
  subst <- combineManySubstitutions s [subst0, subst1, subst2]
  return (ktype, subst, Box c' t')

-- KChkS_dia
synthKind' s _ (Diamond e t) = do
  (innerK, subst2, e') <- synthKind s e
  (subst1, _)  <- checkKind s innerK keffect
  (subst3, t') <- checkKind s t ktype
  subst <- combineManySubstitutions s [subst1, subst2, subst3]
  return (ktype, subst, Diamond e' t')

synthKind' s _ t@(TyCon (internalName -> "Pure")) = do
  -- Create a fresh type variable
  var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") keffect
  return (TyVar var, [], t)

synthKind' s _ t@(TyCon (internalName -> "Handled")) = do
  var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") keffect
  return $ ((FunTy Nothing (TyVar var) (TyVar var)), [], t)

-- KChkS_con
synthKind' s _ t@(TyCon id) = do
  st <- get
  case lookup id (typeConstructors st)  of
    Just (kind', _, _) -> return (kind', [], t)
    Nothing -> do
      mConstructor <- lookupDataConstructor s id
      case mConstructor of
        Just (Forall _ [] [] tDat, _) -> return (tDat, [], t)
        Just _ -> error $ pretty s <> "I'm afraid I can't yet promote the polymorphic data constructor:"  <> pretty id
        Nothing -> throw UnboundTypeConstructor { errLoc = s, errId = id }

-- KChkS_set
synthKind' s overloadToNat t0@(TySet p (elem:elems)) = do
  (k, subst1, elem') <- synthKind' s overloadToNat elem
  results <- mapM (\elem -> checkKind s elem k) elems
  let (substs, elems') = unzip results
  subst <- combineManySubstitutions s (subst1:substs)
  return (TyApp (setConstructor p) k, subst, TySet p (elem':elems'))

-- KChkS_set (empty) -- gives a polymorphic type to the elements
synthKind' s overloadToNat (TySet p []) = do
  var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") ktype
  return (TyApp (setConstructor p) (TyVar var), [], TySet p [])

-- KChkS_sig
synthKind' s _ (TySig t k) = do
  (subst, t') <- checkKind s t k
  return (k, subst, TySig t' k)

synthKind' s overloadToNat (TyCase t branches) | length branches > 0 = do
  -- Synthesise the kind of the guard (which must be the kind of the branches)
  (k, subst, t') <- synthKind' s overloadToNat t
  -- Check the patterns are kinded by the guard kind, and synth the kinds
  -- for the branches
  branchesInfo <-
    forM branches (\(tyPat, tyBranch) -> do
      (subst_i, tyPat') <- checkKind s tyPat k
      (k_i, subst'_i, tyBranch') <- synthKind' s overloadToNat tyBranch
      subst <- combineSubstitutions s subst_i subst'_i
      return ((tyPat', tyBranch'), (subst, (tyBranch', k_i))))
  -- Split up the info
  let (branches', substsAndKinds) = unzip branchesInfo
  let (substs, branchesAndKinds) = unzip substsAndKinds
  substIntermediate <- combineManySubstitutions s (subst:substs)
  -- Check that we can join all the kinds of the branches, and combine all the substitutions
  (kind, substFinal) <- foldM (\(kJoined, subst) (branchTy, k) -> do
        joined <- joinTypes s k kJoined
        case joined of
          Just (kNext, subst', _) -> do
            subst' <- combineSubstitutions s subst subst'
            return (kNext, subst')
          Nothing ->
            throw KindMismatch { errLoc = s, tyActualK = Just branchTy, kExpected = kJoined, kActual = k })
      (snd $ head branchesAndKinds, substIntermediate)
      (tail branchesAndKinds)
  --
  return (kind, substFinal, TyCase t' branches')

synthKind' s _ t =
  throw ImpossibleKindSynthesis { errLoc = s, errTy = t }

synthForOperator :: (?globals :: Globals)
  => Span
  -> Bool -- flag whether overloading to Nat is allowed
  -> TypeOperator
  -> Type
  -> Type
  -> Checker (Kind, Substitution, Type)
synthForOperator s overloadToNat op t1 t2 = do
  if predicateOperation op || closedOperation op
    then do
      (k1, subst1, t1') <- synthKind' s overloadToNat t1
      (k2, subst2, t2') <- synthKind' s overloadToNat t2
      (k3, substK, (inj1, inj2)) <- mguCoeffectTypes s k1 k2

      maybeSubst <- if predicateOperation op
                      then predicateOperatorAtKind s op k3
                      else closedOperatorAtKind s op k3
      case maybeSubst of
        Just subst3 -> do
          subst <- combineManySubstitutions s [subst1, subst2, subst3, substK]
          if predicateOperation op
            then return (kpredicate, subst, TyInfix op (inj1 t1') (inj2 t2'))
            else return (k3, subst, TyInfix op (inj1 t1') (inj2 t2'))

        Nothing -> throw OperatorUndefinedForKind { errLoc = s, errTyOp = op, errK = k1 }
    else throw ImpossibleKindSynthesis { errLoc = s, errTy = TyInfix op t1 t2 }

-- | `closedOperatorAtKind` takes an operator `op` and a kind `k` and returns a
-- substitution if this is a valid operator at kind `k -> k -> k`.
closedOperatorAtKind :: (?globals :: Globals)
  => Span
  -> TypeOperator
  -> Kind
  -> Checker (Maybe Substitution)

-- Nat case
closedOperatorAtKind _ op (TyCon (internalName -> "Nat")) =
  return $ if closedOperation op then Just [] else Nothing

-- Expontentiation on effects also allowed
closedOperatorAtKind s TyOpExpon t = do
  _ <- checkKind s t keffect
  return $ Just []

-- * case
closedOperatorAtKind s TyOpTimes t = do
  -- See if the type is a coeffect
  (result, putChecker) <- peekChecker (checkKind s t kcoeffect)
  case result of
    Left _ -> do
      -- If not, see if the type is an effect
      (result', putChecker') <- peekChecker (checkKind s t keffect)
      case result' of
        -- Not a closed operator at this kind
        Left  _ -> return Nothing
        -- Yes it is an effect type
        Right (subst, _) -> do
          putChecker'
          return $ Just subst
    -- Yes it is a coeffect type
    Right (subst, _) -> do
      putChecker
      return $ Just subst

-- Any other "coeffect operators" case
closedOperatorAtKind s op t | coeffectResourceAlgebraOps op = do
  -- See if the type is a coeffect
  (result, putChecker) <- peekChecker (checkKind s t kcoeffect)
  case result of
    Left _ -> return Nothing
    Right (subst, _) -> do
      putChecker
      return $ Just subst
      --return $ Just (FunTy t (FunTy t t, subst))

closedOperatorAtKind _ op (TyVar _) =
  return $ if closedOperation op then Just [] else Nothing

closedOperatorAtKind _ _ _ = return Nothing

-- | `predicateOperatorAtKind` takes an operator `op` and a kind `k` and returns
-- a substitution if this is a valid operator at kind `k -> k -> kpredicate`.
predicateOperatorAtKind :: (?globals :: Globals) =>
  Span -> TypeOperator -> Kind -> Checker (Maybe Substitution)
predicateOperatorAtKind s op t | predicateOperation op = do
  (result, putChecker) <- peekChecker (checkKind s t kcoeffect)
  case result of
    Left _ -> return Nothing
    Right (subst, _) -> do
      putChecker
      return $ Just subst
predicateOperatorAtKind s op k@(TyVar _) =
    return $ if predicateOperation op then Just [] else Nothing
predicateOperatorAtKind _ _ _ = return Nothing

-- | Determines if a type operator produces results of kind kpredicate.
predicateOperation :: TypeOperator -> Bool
predicateOperation op = (\(_, _, c) -> c) (tyOps op) == kpredicate

-- | Compute the join of two types, if it exists
-- | (including injections in the case of coeffect types)

joinTypes :: (?globals :: Globals)
          => Span
          -> Type
          -> Type
          -> Checker (Maybe (Type, Substitution, Maybe Injections))
joinTypes s t1 t2 = runMaybeT (joinTypes' s t1 t2)

joinTypes' :: (?globals :: Globals)
          => Span
          -> Type
          -> Type
          -> MaybeT Checker (Type, Substitution, Maybe Injections)
joinTypes' s t t' | t == t' = return (t, [], Nothing)

joinTypes' s (FunTy id t1 t2) (FunTy _ t1' t2') = do
  (t1j, subst1, _) <- joinTypes' s t1' t1 -- contravariance
  (t2j, subst2, _) <- joinTypes' s t2 t2'
  subst <- lift $ combineSubstitutions s subst1 subst2
  return (FunTy id t1j t2j, subst, Nothing)

joinTypes' s (Diamond ef1 t1) (Diamond ef2 t2) = do
  (tj, subst0, _) <- joinTypes' s t1 t2
  -- Calculate the effect type for the effects here
  (efty1, subst1, ef1') <- lift $ synthKind s ef1
  (efty2, subst2, ef2') <- lift $ synthKind s ef2
  -- Compute the upper bound on the types
  (efftj, subst3, _) <- joinTypes' s efty1 efty2
  -- Computes the upper bound on the effects
  ej <- lift $ effectUpperBound s efftj ef1' ef2'
  subst <- lift $ combineManySubstitutions s [subst0, subst1, subst2, subst3]
  return (Diamond ej tj, subst, Nothing)

joinTypes' s (Box c t) (Box c' t') = do
  (coeffTy, subst, (inj1, inj2)) <- lift $ mguCoeffectTypesFromCoeffects s c c'
  -- Create a fresh coeffect variable
  topVar <- lift $ freshTyVarInContext (mkId "") coeffTy
  -- Unify the two coeffects into one
  lift $ addConstraint (ApproximatedBy s (inj1 c)  (TyVar topVar) coeffTy)
  lift $ addConstraint (ApproximatedBy s (inj2 c') (TyVar topVar) coeffTy)
  (tUpper, subst', _) <- joinTypes' s t t'
  substFinal <- lift $ combineSubstitutions s subst subst'
  return (Box (TyVar topVar) tUpper, substFinal, Nothing)

-- -- TODO: Replace how this Nat is constructed?
-- OLD APPROACH- WHICH IS A BIT WEIRD... but something in it?
-- joinTypes s (TyInt n) (TyVar m) = do
--     -- Create a fresh coeffect variable
--   let ty = TyCon $ mkId "Nat"
--   var <- freshTyVarInContext m ty
--   -- Unify the two coeffects into one
--   addConstraint (Eq s (TyInt n) (TyVar var) ty)
--   return $ TyInt n

joinTypes' _ (TyVar v) t = do
  st <- get
  case lookup v (tyVarContext st) of
    Just (_, q) | q == InstanceQ || q == BoundQ -> return (t, [(v, SubstT t)], Nothing)
    -- Occurs if an implicitly quantified variable has arisen
    Nothing -> return (t, [(v, SubstT t)], Nothing)
    -- Don't unify with universal variables
    _ -> fail "Cannot unify with a universal"

joinTypes' s t1 t2@(TyVar _) = joinTypes' s t2 t1

joinTypes' s (TyApp t1 t2) (TyApp t1' t2') = do
  (t1'', subst1, _) <- joinTypes' s t1 t1'
  (t2'', subst2, _) <- joinTypes' s t2 t2'
  subst <- lift $ combineSubstitutions s subst1 subst2
  return (TyApp t1'' t2'', subst, Nothing)

joinTypes' s t1 t2 = do
  st <- get
  (isCoeffect1, putChecker1) <- lift $ attemptChecker (checkKind s t1 kcoeffect)
  (isCoeffect2, putChecker2) <- lift $ attemptChecker (checkKind s t2 kcoeffect)
  -- Case where the two types are actually coeffect types
  if isCoeffect1 && isCoeffect2
    then lift $ do
      -- Find the most general unifier for the types
      putChecker1
      putChecker2
      (jcoeffTy, subst, injections) <- mguCoeffectTypes s t1 t2
      return (jcoeffTy, subst, Just injections)
    else
      -- Fall through
      fail "No upper bound"

-- Universally quantifies everything in a context.
universify :: Ctxt Kind -> Ctxt (Type, Quantifier)
universify = map (second (\k -> (k, ForallQ)))

synthKindAssumption :: (?globals :: Globals) => Span -> Assumption -> Checker (Maybe Type, Substitution)
synthKindAssumption _ (Linear _) = return (Nothing, [])
synthKindAssumption s (Discharged _ c) = do
  (t, subst, _) <- synthKind s c
  return (Just t, subst)
synthKindAssumption s (Ghost _ c) = do
  (t, subst, _) <- synthKind s c
  return (Just t, subst)

-- Find the most general unifier of two coeffects
-- This is an effectful operation which can update the coeffect-kind
-- contexts if a unification resolves a variable
mguCoeffectTypesFromCoeffects :: (?globals :: Globals)
  => Span
  -> Type
  -> Type
  -> Checker (Type, Substitution, (Type -> Type, Type -> Type))
mguCoeffectTypesFromCoeffects s c1 c2 = do
  (coeffTy1, subst1, _) <- synthKind s c1
  (coeffTy2, subst2, _) <- synthKind s c2
  (coeffTy, subst3, res) <- mguCoeffectTypes s coeffTy1 coeffTy2
  subst <- combineManySubstitutions s [subst1, subst2, subst3]
  return (coeffTy, subst, res)
