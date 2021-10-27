{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Kind checking and inference algorithms
-- | as well as the core type variable unifier
module Language.Granule.Checker.Kinding where

import Control.Arrow (second)
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Data.Functor.Identity (runIdentity)
import Data.Maybe (fromMaybe)

import Language.Granule.Context

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Helpers (freeVars)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Checker.Effects (effectTop, effectUpperBound)
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Primitives
    (closedOperation, coeffectResourceAlgebraOps, tyOps)
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.Variables
--import Language.Granule.Checker.Normalise

import Language.Granule.Utils

type Injections = (Coeffect -> Coeffect, Coeffect -> Coeffect)

-- | Check the kind of a definition
-- | NOTE: Currently we expect that a type scheme has kind ktype
kindCheckDef :: (?globals :: Globals) => Def v t -> Checker (Def v t)
kindCheckDef (Def s id rf eqs (Forall s' quantifiedVariables constraints ty)) = do
  -- Make local context of universal variables
  let localTyVarContext = universify quantifiedVariables

  -- Set up the quantified variables in the type variable context
  modify (\st -> st { tyVarContext = localTyVarContext })
  -- Check that all constraints have kind Predicate
  forM_ constraints $ \constraint -> checkKind s constraint kpredicate

  ty <- replaceSynonyms ty

  -- Check kind of signature is indeed Type
  (unifiers, tyElaborated) <- checkKind s ty ktype

  -- Rewrite the quantified variables with their possibly updated kinds (inferred)
  qVars <- mapM (\(v, a) -> substitute unifiers a >>= (\b -> return (v, b))) quantifiedVariables
  modify (\st -> st { tyVarContext = [] })

  -- Update the def with the resolved quantifications
  return (Def s id rf eqs (Forall s' qVars constraints tyElaborated))

  where
    -- Universally quantifies everything in a context.
    universify :: Ctxt Kind -> Ctxt (Type, Quantifier)
    universify = map (second (\k -> (k, ForallQ)))


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
    Just (jk, subst, inj) -> do
      -- Now actually do the check of kind on the inner part of the ty sig
      (subst', t') <- checkKind s t jk
      subst2 <- combineSubstitutions s subst subst'
      case inj of
        Nothing           -> return (subst2, TySig t' jk)
        -- Apply the left injection
        Just (inj1, inj2) -> return (subst2, TySig (inj1 t') jk)
    Nothing -> throw KindMismatch { errLoc = s, tyActualK = Just t, kExpected = k, kActual = k' }

-- KChck_Nat
-- "Nat" belonds to Coeffect, Effect, and Type kinds
checkKind s t@(TyCon (internalName -> "Nat")) (TyCon (internalName -> "Coeffect")) =
  return ([], t)
checkKind s t@(TyCon (internalName -> "Nat")) (TyCon (internalName -> "Effect")) =
  return ([], t)
checkKind s t@(TyCon (internalName -> "Nat")) (Type 0) =
  return ([], t)

checkKind s t@(TyCon (internalName -> "Infinity")) (TyApp (TyCon (internalName -> "Ext")) _) =
  return ([], t)

-- Fall through to synthesis if checking can not be done.
checkKind s t k = do
  -- Synth
  (k', subst1, t') <- synthKind s t
  -- See if we can do a join (equality+) on the synthed kind and the one coming as specification here.
  join <- joinTypesNoMGU s k k'
  case join of
    Just (_, subst2, _) -> do
      substFinal <- combineSubstitutions s subst1 subst2
      return (substFinal, t')
    Nothing -> throw KindMismatch { errLoc = s, tyActualK = Just t, kExpected = k, kActual = k' }

------------------------------------------------------------

-- Represents how to resolve a grade which has no type annotation
data ResolutionConfig =
    GradeToNat              -- ^ Resolve untyped grades as Nat
   | GradeToPolyAsCoeffect  -- ^ Resolve untyped grades to a fresh unification variable which is Coeffect kinded
   | GradeToPolyAsEffect    -- ^ Resolve untyped grades to a fresh unification variable which is Effect kinded
  deriving Eq

defaultResolutionBehaviour :: Type -> ResolutionConfig
defaultResolutionBehaviour t =
  if (not (containsTypeSig t))
    -- no type signatures here so try to guess grades as Nat (often a bad choice!)
    then GradeToNat
    -- if there is a type signature then try to treat untyped grades as coeffect by default
    else GradeToPolyAsCoeffect

-- Given `synthKind gam t` it synthesis a `k` such that `gam |- t :: k` and
-- returns a substitution and an elebaroted type `t'` along with it.
synthKind :: (?globals :: Globals) =>
  Span -> Type -> Checker (Kind, Substitution, Type)
synthKind s t =
  synthKindWithConfiguration s (defaultResolutionBehaviour t) t

-- Parameterisable core of `synthKind`
synthKindWithConfiguration :: (?globals :: Globals) =>
     Span
  -> ResolutionConfig -- Special flag: explains how to resolve untyped grades
  -> Type
  -> Checker (Kind, Substitution, Type)

-- KChkS_var and KChkS_instVar
synthKindWithConfiguration s config t@(TyVar x) = do
  st <- get
  case lookup x (tyVarContext st) of
    Just (k, _) -> return (k, [], t)
    Nothing     -> throw UnboundTypeVariable { errLoc = s, errId = x }

-- -- KChkS_fun
--
--      t1 => k    t2 <= k
--   ----------------------- Fun
--        t1 -> t2 => k

synthKindWithConfiguration s config (FunTy name t1 t2) = do
  (k, subst1, t1') <- synthKindWithConfiguration s config t1
  (subst2   , t2') <- checkKind s t2 k
  subst <- combineSubstitutions s subst1 subst2
  return (k, subst, FunTy name t1' t2')

-- KChkS_pair
synthKindWithConfiguration s config (TyApp (TyApp (TyCon (internalName -> ",,")) t1) t2) = do
  (k1, subst1, t1') <- synthKindWithConfiguration s config t1
  (k2, subst2, t2') <- synthKindWithConfiguration s config t2
  subst <- combineSubstitutions s subst1 subst2
  return (TyApp (TyApp (TyCon $ mkId ",,") k1) k2, subst, TyApp (TyApp (TyCon $ mkId ",,") t1') t2')

-- KChkS_SetKind
synthKindWithConfiguration s config (TyApp (TyCon (internalName -> "Set")) t) = do
  (k, subst, t') <- synthKindWithConfiguration s config t
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
synthKindWithConfiguration s config (TyApp t1 t2) = do
  (funK, subst1, t1') <- synthKindWithConfiguration s config t1
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
synthKindWithConfiguration s config (TyInfix TyOpInterval t1 t2) = do
  (coeffTy1, subst1, t1') <- synthKindWithConfiguration s config t1
  (coeffTy2, subst2, t2') <- synthKindWithConfiguration s config t2
  (jcoeffTy, subst3, (inj1, inj2)) <- mguCoeffectTypes s coeffTy1 coeffTy2
  subst <- combineManySubstitutions s [subst1, subst2, subst3]
  -- Apply injections in the elaborated term
  return (TyApp (tyCon "Interval") jcoeffTy, subst, TyInfix TyOpInterval (inj1 t1') (inj2 t2'))

-- KChkS_predOp
synthKindWithConfiguration s config t@(TyInfix op t1 t2) =
  synthForOperator s config op t1 t2

-- KChkS_int
synthKindWithConfiguration s _ t@(TyInt n) = do
  return (TyCon (Id "Nat" "Nat"), [], t)

-- KChkS_grade [with type already resolved]
synthKindWithConfiguration s config t@(TyGrade (Just k) n) =
  return (k, [], t)

-- KChkS_grade [type not resolve]
synthKindWithConfiguration s config t@(TyGrade Nothing n) = do
  case config of
    GradeToPolyAsCoeffect -> do
      var <- freshTyVarInContext (mkId $ "semiring[" <> pretty (startPos s) <> "]") kcoeffect
      return (TyVar var, [], t)
    GradeToPolyAsEffect -> do
      var <- freshTyVarInContext (mkId $ "monoid[" <> pretty (startPos s) <> "]") keffect
      return (TyVar var, [], t)
    GradeToNat ->
      return (tyCon "Nat", [], TyInt n)

-- KChkS_box
synthKindWithConfiguration s _ (Box c t) = do
  -- Deal with the grade term
  (coeffTy, subst0, c') <- synthKindWithConfiguration s (defaultResolutionBehaviour c) c
  (subst1, _) <- checkKind s coeffTy kcoeffect
  -- Then the inner type
  (subst2, t') <- checkKind s t ktype
  subst <- combineManySubstitutions s [subst0, subst1, subst2]
  return (ktype, subst, Box c' t')

-- KChkS_dia
synthKindWithConfiguration s _ (Diamond e t) = do
  (innerK, subst2, e') <- synthKind s e
  (subst1, _)  <- checkKind s innerK keffect
  (subst3, t') <- checkKind s t ktype
  subst <- combineManySubstitutions s [subst1, subst2, subst3]
  return (ktype, subst, Diamond e' t')

synthKindWithConfiguration s _ (Star g t) = do
  (guaranTy, subst0, g') <- synthKindWithConfiguration s (defaultResolutionBehaviour g) g
  (subst1, _) <- checkKind s guaranTy kguarantee
  (subst2, t') <- checkKind s t ktype
  subst <- combineManySubstitutions s [subst0, subst1, subst2]
  return (ktype, subst, Star g' t')

synthKindWithConfiguration s _ t@(TyCon (internalName -> "Pure")) = do
  -- Create a fresh type variable
  var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") keffect
  return (TyVar var, [], t)

synthKindWithConfiguration s _ t@(TyCon (internalName -> "Handled")) = do
  var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") keffect
  return $ ((FunTy Nothing (TyVar var) (TyVar var)), [], t)

synthKindWithConfiguration s _ t@(TyCon (internalName -> "Infinity")) = do
  var <- freshTyVarInContext (mkId $ "s") kcoeffect
  return (TyApp (TyCon $ mkId "Ext") (TyVar var), [], t)

-- KChkS_con
synthKindWithConfiguration s _ t@(TyCon id) = do
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
synthKindWithConfiguration s config t0@(TySet p (elem:elems)) = do
  (k, subst1, elem') <- synthKindWithConfiguration s config elem
  results <- mapM (\elem -> checkKind s elem k) elems
  let (substs, elems') = unzip results
  subst <- combineManySubstitutions s (subst1:substs)
  return (TyApp (setConstructor p) k, subst, TySet p (elem':elems'))

-- KChkS_set (empty) -- gives a polymorphic type to the elements
synthKindWithConfiguration s config (TySet p []) = do
  var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") ktype
  return (TyApp (setConstructor p) (TyVar var), [], TySet p [])

-- KChkS_sig
synthKindWithConfiguration s _ (TySig t k) = do
  (subst, t') <- checkKind s t k
  return (k, subst, TySig t' k)

synthKindWithConfiguration s config (TyCase t branches) | length branches > 0 = do
  -- Synthesise the kind of the guard (which must be the kind of the branches)
  (k, subst, t') <- synthKindWithConfiguration s config t
  -- Check the patterns are kinded by the guard kind, and synth the kinds
  -- for the branches
  branchesInfo <-
    forM branches (\(tyPat, tyBranch) -> do
      (subst_i, tyPat') <- checkKind s tyPat k
      (k_i, subst'_i, tyBranch') <- synthKindWithConfiguration s config tyBranch
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

-- Type-level rationals, live in Q (rationals)
synthKindWithConfiguration s config t@(TyRational _) = do
  return (TyCon $ mkId "Q", [], t)

synthKindWithConfiguration s _ t =
  throw ImpossibleKindSynthesis { errLoc = s, errTy = t }

synthForOperator :: (?globals :: Globals)
  => Span
  -> ResolutionConfig
  -> TypeOperator
  -> Type
  -> Type
  -> Checker (Kind, Substitution, Type)
synthForOperator s config op t1 t2 = do
  if predicateOperation op || closedOperation op
    then do
      (k1, subst1, t1') <- synthKindWithConfiguration s config t1
      (k2, subst2, t2') <- synthKindWithConfiguration s config t2
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

-- TODO: ghost variables, do we need to worry about substitution?
closedOperatorAtKind s TyOpConverge t = do
  _ <- checkKind s t kcoeffect
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

-- Join types but force grades to be equal
joinTypesForEqualCoeffectGrades :: (?globals :: Globals)
          => Span
          -> Type
          -> Type
          -> Checker (Maybe (Type, Substitution, Maybe Injections))
joinTypesForEqualCoeffectGrades s t1 t2 = runMaybeT (joinTypes'' s t1 t2 Eq)

-- Wrapper over `jointTypes'` that uses approximation
joinTypes' :: (?globals :: Globals)
          => Span
          -> Type
          -> Type
          -> MaybeT Checker (Type, Substitution, Maybe Injections)
joinTypes' s t t' = joinTypes'' s t t' ApproximatedBy

joinTypes'' :: (?globals :: Globals)
          => Span
          -> Type
          -> Type
          -> (Span -> Type -> Type -> Type -> Constraint) -- how to build a constraint for grades
          -> MaybeT Checker (Type, Substitution, Maybe Injections)
joinTypes'' s t t' rel | t == t' = return (t, [], Nothing)

joinTypes'' s (FunTy id t1 t2) (FunTy _ t1' t2') rel = do
  (t1j, subst1, _) <- joinTypes'' s t1' t1 rel -- contravariance
  (t2j, subst2, _) <- joinTypes'' s t2 t2' rel
  subst <- lift $ combineSubstitutions s subst1 subst2
  return (FunTy id t1j t2j, subst, Nothing)

joinTypes'' s (Diamond ef1 t1) (Diamond ef2 t2) rel = do
  (tj, subst0, _) <- joinTypes'' s t1 t2 rel
  -- Calculate the effect type for the effects here
  (efty1, subst1, ef1') <- lift $ synthKind s ef1
  (efty2, subst2, ef2') <- lift $ synthKind s ef2
  -- Compute the upper bound on the types
  (efftj, subst3, _) <- joinTypes'' s efty1 efty2 rel
  -- Computes the upper bound on the effects
  ej <- lift $ effectUpperBound s efftj ef1' ef2'
  subst <- lift $ combineManySubstitutions s [subst0, subst1, subst2, subst3]
  return (Diamond ej tj, subst, Nothing)

joinTypes'' s (Box c t) (Box c' t') rel = do
  (coeffTy, subst, (inj1, inj2)) <- lift $ mguCoeffectTypesFromCoeffects s c c'
  -- Create a fresh coeffect variable
  topVar <- lift $ freshTyVarInContext (mkId "") coeffTy
  -- Unify the two coeffects into one
  lift $ addConstraint (rel s (inj1 c)  (TyVar topVar) coeffTy)
  lift $ addConstraint (rel s (inj2 c') (TyVar topVar) coeffTy)
  (tUpper, subst', _) <- joinTypes'' s t t' rel
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

joinTypes'' s (TyVar v) t rel = do
  subst <- lift $ unification s v t rel
  return (t, subst, Nothing)

joinTypes'' s t1 t2@(TyVar _) rel = joinTypes'' s t2 t1 rel

joinTypes'' s (TyApp t1 t2) (TyApp t1' t2') rel = do
  (t1'', subst1, _) <- joinTypes'' s t1 t1' rel
  (t2'', subst2, _) <- joinTypes'' s t2 t2' rel
  subst <- lift $ combineSubstitutions s subst1 subst2
  return (TyApp t1'' t2'', subst, Nothing)

joinTypes'' s t1 t2 rel = do
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

-- | Compute the join of two types, if it exists
-- | (without using most general unifier for coeffects)
joinTypesNoMGU :: (?globals :: Globals)
          => Span
          -> Type
          -> Type
          -> Checker (Maybe (Type, Substitution, Maybe Injections))
joinTypesNoMGU s t1 t2 = runMaybeT (joinTypesNoMGU' s t1 t2)


-- Wrapper over `jointTypesNoMGU'` that uses approximation
joinTypesNoMGU' :: (?globals :: Globals)
          => Span
          -> Type
          -> Type
          -> MaybeT Checker (Type, Substitution, Maybe Injections)
joinTypesNoMGU' s t t' = joinTypesNoMGU'' s t t' ApproximatedBy

joinTypesNoMGU'' :: (?globals :: Globals)
          => Span
          -> Type
          -> Type
          -> (Span -> Type -> Type -> Type -> Constraint) -- how to build a constraint for grades
          -> MaybeT Checker (Type, Substitution, Maybe Injections)
joinTypesNoMGU'' s t t' rel | t == t' = return (t, [], Nothing)

joinTypesNoMGU'' s (FunTy id t1 t2) (FunTy x t1' t2') rel =
  joinTypes'' s (FunTy id t1 t2) (FunTy x t1' t2') rel

joinTypesNoMGU'' s (Diamond ef1 t1) (Diamond ef2 t2) rel =
  joinTypes'' s (Diamond ef1 t1) (Diamond ef2 t2) rel

joinTypesNoMGU'' s (Box c t) (Box c' t') rel =
  joinTypes'' s (Box c t) (Box c' t') rel

joinTypesNoMGU'' s (TyVar v) t rel =
  joinTypes'' s (TyVar v) t rel

joinTypesNoMGU'' s t1 t2@(TyVar _) rel =
  joinTypes'' s t1 t2 rel

joinTypesNoMGU'' s (TyApp t1 t2) (TyApp t1' t2') rel =
  joinTypes'' s (TyApp t1 t2) (TyApp t1' t2') rel

joinTypesNoMGU'' s t1 t2 rel = do
  fail "No upper bound"


synthKindAssumption :: (?globals :: Globals) => Span -> Assumption -> Checker (Maybe Type, Substitution)
synthKindAssumption _ (Linear _) = return (Nothing, [])
synthKindAssumption s (Discharged _ c) = do
  (t, subst, _) <- synthKind s c
  return (Just t, subst)
synthKindAssumption s (Ghost c) = do
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

-- Compute the most general unification between two coeffect types
-- which produces their unification, a substitution, and a pair of injections
-- for terms of the previous types. i.e.,
--  if `mguCoeffectTypes t1 t2` yields type `t3` and injections `(i1, i2)`
--  then if `r1 : t1` and `r2 : t2` then `i1 r1 : t3` and `i2 t2 : t3`.

mguCoeffectTypes :: (?globals :: Globals)
                 => Span -> Type -> Type -> Checker (Type, Substitution, Injections)
mguCoeffectTypes s t1 t2 = do
  upper <- mguCoeffectTypes' s t1 t2
  case upper of
    Just x -> return x
    -- Cannot unify so form a product
    Nothing -> return
      (TyApp (TyApp (TyCon (mkId ",,")) t1) t2, [],
                  (\x -> cProduct x (TyGrade (Just t2) 1), \x -> cProduct (TyGrade (Just t1) 1) x))

-- Inner definition which does not throw its error, and which operates on just the types
mguCoeffectTypes' :: (?globals :: Globals)
  => Span -> Type -> Type -> Checker (Maybe (Type, Substitution, (Coeffect -> Coeffect, Coeffect -> Coeffect)))

-- Trivial case
mguCoeffectTypes' s t t' | t == t' = return $ Just (t, [], (id, id))

mguCoeffectTypes' s (TyVar kvar1) kv2 = do
  subst <- unification s kvar1 kv2 Eq
  return $ Just (TyVar kvar1, subst, (id, id))

mguCoeffectTypes' s kv1 (TyVar kv2) = do
  mguCoeffectTypes' s (TyVar kv2) kv1

{-- TODO: DEL
-- Both are variables
mguCoeffectTypes' s (TyVar kv1) (TyVar kv2) | kv1 /= kv2 = do
  st <- get
  case (lookup kv1 (tyVarContext st), lookup kv2 (tyVarContext st))  of
    (Nothing, _) -> throw $ UnboundVariableError s kv1
    (_, Nothing) -> throw $ UnboundVariableError s kv2
    (Just (TyCon kcon1, _), Just (TyCon kcon2, InstanceQ)) | kcon1 == kcon2 -> do
      substIntoTyVarContext kv2 (TyVar kv1)
      return $ Just (TyVar kv1, [(kv2, SubstT $ TyVar kv1)], (id, id))

    (Just (TyCon kcon1, InstanceQ), Just (TyCon kcon2, _)) | kcon1 == kcon2 -> do
      substIntoTyVarContext kv1 (TyVar kv2)
      return $ Just (TyVar kv2, [(kv1, SubstT $ TyVar kv2)], (id, id))

    (Just (TyCon kcon1, ForallQ), Just (TyCon kcon2, ForallQ)) | kcon1 == kcon2 ->
      throw $ UnificationFail s kv2 (TyVar kv1) (TyCon kcon1) False

    (Just (k', _), Just (k, _)) ->
      throw $ UnificationFail s kv2 (TyVar kv1) k' False

-- Left-hand side is a poly variable, but Just is concrete
mguCoeffectTypes' s (TyVar kv1) coeffTy2 = do
  st <- get

  case lookup kv1 (tyVarContext st) of
    Nothing -> throw $ UnboundVariableError s kv1

    -- Cannot unify if the type variable is univrssal
    Just (k, ForallQ) ->
      throw $ UnificationFail s kv1 coeffTy2 k True

    -- Can unify if the type variable is a unification var
    Just (k, _) -> do -- InstanceQ or BoundQ
      substIntoTyVarContext kv1 coeffTy2
      return $ Just (coeffTy2, [(kv1, SubstT coeffTy2)], (id, id))

-- Right-hand side is a poly variable, but Linear is concrete
mguCoeffectTypes' s coeffTy1 (TyVar kv2) = do
  mguCoeffectTypes' s (TyVar kv2) coeffTy1
  -}

-- Ext cases
-- unify (Ext t) (Ext t') = Ext (unify t t')
mguCoeffectTypes' s (isExt -> Just t) (isExt -> Just t') = do
  coeffecTyUpper <- mguCoeffectTypes' s t t'
  case coeffecTyUpper of
    Just (upperTy, subst, (inj1, inj2)) -> do
      return $ Just (TyApp (TyCon $ mkId "Ext") upperTy, subst, (inj1, inj2))
    Nothing -> return Nothing

-- unify (Ext t) t' = Ext (unify t t')
mguCoeffectTypes' s (isExt -> Just t) t' = do
  -- liftIO $ putStrLn $ "unify (Ext " <> pretty t <> ") with " <> pretty t'
  coeffecTyUpper <- mguCoeffectTypes' s t t'
  case coeffecTyUpper of
    Just (upperTy, subst, (inj1, inj2)) -> do
      return $ Just (TyApp (TyCon $ mkId "Ext") upperTy, subst, (inj1, inj2))
    Nothing -> return Nothing

-- unify t (Ext t') = Ext (unify t t')
mguCoeffectTypes' s t (isExt -> Just t') = do
  -- liftIO $ putStrLn $ "unify " <> pretty t <> " with (Ext " <> pretty t' <> ")"
  coeffecTyUpper <- mguCoeffectTypes' s t t'
  case coeffecTyUpper of
    Just (upperTy, subst, (inj1, inj2)) -> do
      return $ Just (TyApp (TyCon $ mkId "Ext") upperTy, subst, (inj1, inj2))
    Nothing -> return Nothing

-- `Nat` can unify with `Q` to `Q`
mguCoeffectTypes' s (TyCon (internalName -> "Q")) (TyCon (internalName -> "Nat")) =
    return $ Just $ (TyCon $ mkId "Q", [], (id, inj))
  where inj =  runIdentity . typeFoldM baseTypeFold
                { tfTyInt = \x -> return $ TyRational (fromInteger . toInteger $ x) }

mguCoeffectTypes' s (TyCon (internalName -> "Nat")) (TyCon (internalName -> "Q")) =
    return $ Just $ (TyCon $ mkId "Q", [], (inj, id))
  where inj = runIdentity . typeFoldM baseTypeFold
                { tfTyInt = \x -> return $ TyRational (fromInteger . toInteger $ x) }

-- `Nat` can unify with `Ext Nat` to `Ext Nat`
mguCoeffectTypes' s t (TyCon (internalName -> "Nat")) | t == extendedNat =
  return $ Just (extendedNat, [], (id, id))

mguCoeffectTypes' s (TyCon (internalName -> "Nat")) t | t == extendedNat =
  return $ Just (extendedNat, [], (id, id))

-- Unifying a product of (t, t') with t yields (t, t') [and the symmetric versions]
mguCoeffectTypes' s coeffTy1@(isProduct -> Just (t1, t2)) coeffTy2 | t1 == coeffTy2 =
  return $ Just (coeffTy1, [], (id, \x -> cProduct x (TyGrade (Just t2) 1)))

mguCoeffectTypes' s coeffTy1@(isProduct -> Just (t1, t2)) coeffTy2 | t2 == coeffTy2 =
  return $ Just (coeffTy1, [], (id, \x -> cProduct (TyGrade (Just t1) 1) x))

mguCoeffectTypes' s coeffTy1 coeffTy2@(isProduct -> Just (t1, t2)) | t1 == coeffTy1 =
  return $ Just (coeffTy2, [], (\x -> cProduct x (TyGrade (Just t2) 1), id))

mguCoeffectTypes' s coeffTy1 coeffTy2@(isProduct -> Just (t1, t2)) | t2 == coeffTy1 =
  return $ Just (coeffTy2, [], (\x -> cProduct (TyGrade (Just t1) 1) x, id))

-- Unifying with an interval
mguCoeffectTypes' s coeffTy1 coeffTy2@(isInterval -> Just t') | coeffTy1 == t' =
  return $ Just (coeffTy2, [], (\x -> TyInfix TyOpInterval x x, id))

mguCoeffectTypes' s coeffTy1@(isInterval -> Just t') coeffTy2 | coeffTy2 == t' =
  return $ Just (coeffTy1, [], (id, \x -> TyInfix TyOpInterval x x))

-- Unifying inside an interval (recursive case)

-- Both intervals
mguCoeffectTypes' s (isInterval -> Just t) (isInterval -> Just t') = do
-- See if we can recursively unify inside an interval
  -- This is done in a local type checking context as `mguCoeffectType` can cause unification
  coeffecTyUpper <- mguCoeffectTypes' s t t'
  case coeffecTyUpper of
    Just (upperTy, subst, (inj1, inj2)) -> do
      return $ Just (TyApp (TyCon $ mkId "Interval") upperTy, subst, (inj1', inj2'))
            where
              inj1' = runIdentity . typeFoldM baseTypeFold { tfTyInfix = \op c1 c2 -> return $ case op of TyOpInterval -> TyInfix op (inj1 c1) (inj1 c2); _ -> TyInfix op c1 c2 }
              inj2' = runIdentity . typeFoldM baseTypeFold { tfTyInfix = \op c1 c2 -> return $ case op of TyOpInterval -> TyInfix op (inj2 c1) (inj2 c2); _ -> TyInfix op c1 c2 }
    Nothing -> return Nothing

mguCoeffectTypes' s t (isInterval -> Just t') = do
  -- See if we can recursively unify inside an interval
  -- This is done in a local type checking context as `mguCoeffectType` can cause unification
  coeffecTyUpper <- mguCoeffectTypes' s t t'
  case coeffecTyUpper of
    Just (upperTy, subst, (inj1, inj2)) ->
      return $ Just (TyApp (TyCon $ mkId "Interval") upperTy, subst, (\x -> TyInfix TyOpInterval (inj1 x) (inj1 x), inj2'))
            where inj2' = runIdentity . typeFoldM baseTypeFold { tfTyInfix = \op c1 c2 -> return $ case op of TyOpInterval -> TyInfix op (inj2 c1) (inj2 c2); _ -> TyInfix op c1 c2 }

    Nothing -> return Nothing

mguCoeffectTypes' s (isInterval -> Just t') t = do
  -- See if we can recursively unify inside an interval
  -- This is done in a local type checking context as `mguCoeffectType` can cause unification
  coeffecTyUpper <- mguCoeffectTypes' s t' t
  case coeffecTyUpper of
    Just (upperTy, subst, (inj1, inj2)) ->
      return $ Just (TyApp (TyCon $ mkId "Interval") upperTy, subst, (inj1', \x -> TyInfix TyOpInterval (inj2 x) (inj2 x)))
            where inj1' = runIdentity . typeFoldM baseTypeFold { tfTyInfix = \op c1 c2 -> return $ case op of TyOpInterval -> TyInfix op (inj1 c1) (inj1 c2); _ -> TyInfix op c1 c2 }

    Nothing -> return Nothing


-- No way to unify (outer function will take the product)
mguCoeffectTypes' s coeffTy1 coeffTy2 = return Nothing


cProduct :: Type -> Type -> Type
cProduct x y = TyApp (TyApp (TyCon (mkId ",,")) x) y

--
requiresSolver :: (?globals :: Globals) => Span -> Type -> Checker Bool
requiresSolver s ty = do
  (result, putChecker) <- peekChecker (checkKind s ty kcoeffect <|> checkKind s ty keffect)
  case result of
    -- Checking as coeffect or effect caused an error so ignore
    Left _  -> return False
    Right _ -> putChecker >> return True


-- | Find out whether a coeffect if flattenable, and if so get the operation
-- | used to represent flattening on the grades
flattenable :: (?globals :: Globals)
            => Type -> Type -> Checker (Maybe ((Coeffect -> Coeffect -> Coeffect), Substitution, Type))
flattenable t1 t2
 | t1 == t2 = case t1 of
    t1 | t1 == extendedNat -> return $ Just (TyInfix TyOpTimes, [], t1)

    TyCon (internalName -> "Nat")   -> return $ Just (TyInfix TyOpTimes, [], t1)
    TyCon (internalName -> "Level") -> return $ Just (TyInfix TyOpMeet, [], t1)
    TyCon (internalName -> "Sec") -> return $ Just (TyInfix TyOpMeet, [], t1)

    TyApp (TyCon (internalName -> "Interval")) t ->  flattenable t t

    -- Sets can use multiply to fold two levels
    (isSet -> Just (elemType, polarity)) -> return $ Just (TyInfix TyOpTimes, [], t1)

    _ -> return $ Nothing
 | otherwise =
      case (t1, t2) of
        (isInterval -> Just t, TyCon (internalName -> "LNL")) | t == extendedNat ->
          return $ Just (TyInfix TyOpTimes, [], TyApp (TyCon $ mkId "Interval") extendedNat)

        (TyCon (internalName -> "LNL"), isInterval -> Just t) | t == extendedNat ->
          return $ Just (TyInfix TyOpTimes, [], TyApp (TyCon $ mkId "Interval") extendedNat)

        (t1, TyCon (internalName -> "Nat")) | t1 == extendedNat ->
          return $ Just (TyInfix TyOpTimes, [], t1)

        (TyCon (internalName -> "Nat"), t2) | t2 == extendedNat ->
          return $ Just (TyInfix TyOpTimes, [], t2)

        (t1, t2) -> do
          -- If we have a unification, then use the flattenable
          jK <- mguCoeffectTypes' nullSpan t1 t2
          case jK of
            Just (t, subst, (inj1, inj2)) -> do
              flatM <- flattenable t t
              case flatM of
                Just (op, subst', t) ->
                  return $ Just (\c1 c2 -> op (inj1 c1) (inj2 c2), subst', t)
                Nothing      -> return $ Just (cProduct, subst, TyCon (mkId ",,") .@ t1 .@ t2)
            Nothing        -> return $ Just (cProduct, [], TyCon (mkId ",,") .@ t1 .@ t2)

-- | Defines what it means to unify a variable
--   given by the second parameter with a type given
--   by the third. Checks quantification issues etc.

--  This is abstracted for use in various places
unification :: (?globals :: Globals)
          => Span
          -> Id
          -> Type
          -> (Span -> Type -> Type -> Type -> Constraint) -- how to build a constraint for grades
          -> Checker Substitution
unification s var1 typ2 rel = do
  checkerState <- get
  case lookup var1 (tyVarContext checkerState) of
    -- Unknown variable
    Nothing -> throw UnboundTypeVariable { errLoc = s, errId = var1 }

    Just (kind1, quantifier1) -> do
      -----------
      debugM "unifier" $ "Unifying variable @ " <> pretty s <> " ("
              <> pretty var1 <> " : " <> pretty kind1 <> " as " <> pretty quantifier1
              <> ")\n\t against type: " <> pretty typ2
      -----------
      -- Case on the quantification mode of this variable
      case quantifier1 of
        -- * BoundQ
        BoundQ -> error $ "boundq deprecated"

        -- * Universal quantifier
        ForallQ ->
          case typ2 of
            -- Same variable so unification accepted
            (TyVar var2) | internalName var1 == internalName var2 -> return []
            -- A different type variable, unification allowed if this is
            -- a unification variable and we are making the unification
            -- in the opposite direction
            (TyVar var2) -> do
              case lookup var2 (tyVarContext checkerState) of
              -- Unknown variable
                Nothing -> throw UnboundTypeVariable { errLoc = s, errId = var2 }

                Just (kind2, quantifier2) -> do
                  case quantifier2 of
                    InstanceQ -> do
                      -- Join kinds
                      joinedKindM <- joinTypes s kind1 kind2
                      case joinedKindM of
                        Nothing -> throw $ KindsNotEqual s kind1 kind2
                        Just (kind, subst, _) -> do

                          -- Types which need solver handling (effects and coeffects)
                          -- need to have constraints registered
                          whenM (requiresSolver s kind)
                            (addConstraint (rel s (TyVar var1) (TyVar var2) kind))

                          -- Local substitution of var2 for the universal var1
                          let localSubst = (var2, SubstT (TyVar var1))
                          -- Apply thhis unification result to the type variable context
                          substIntoTyVarContext var2 (TyVar var1)

                          return (localSubst : subst)

                    _ -> throw $ UnificationFail s var1 typ2 kind1 False

            -- Not a matching tyvar
            _ -> do
              -- Types which need solver handling (effects and coeffects)
              -- need to have constraints registered
              ifM (requiresSolver s kind1)
                -- Create solver constraint and let things get sorted there
                (addConstraint (rel s (TyVar var1) typ2 kind1) >> return [])
                -- This ultimately mostly likely represent a general unification failure
                (throw $ UnificationFail s var1 typ2 kind1 False)

        -- * Unification variable
        InstanceQ -> do
          -- Join kinds
          (kind2, subst1, _) <- synthKind s typ2
          joinedKindM <- joinTypes s kind1 kind2
          case joinedKindM of
            Nothing -> throw $ KindsNotEqual s kind1 kind2
            Just (kind, subst2, _) -> do

              -- Do an occurs check for types
              case kind of
                -- loop in type
                Type _ | var1 `elem` freeVars typ2 ->
                  throw OccursCheckFail { errLoc = s, errVar = var1, errTy = typ2 }
                -- loop in higher type
                FunTy _ _ (Type _) | var1 `elem` freeVars typ2 ->
                  throw OccursCheckFail { errLoc = s, errVar = var1, errTy = typ2 }
                _ -> return ()

              -- Local substitution
              let localSubst = (var1, SubstT typ2)

              -- Types which need solver handling (effects and coeffects)
              -- need to have constraints registered
              whenM (requiresSolver s kind)
                  -- Create solver constraint
                 (addConstraint (rel s (TyVar var1) typ2 kind))

              -- Apply thhis unification result to the type variable context
              substIntoTyVarContext var1 typ2

              subst <- combineSubstitutions s subst1 subst2
              return (localSubst : subst)