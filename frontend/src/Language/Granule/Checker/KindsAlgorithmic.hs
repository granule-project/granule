module Language.Granule.Checker.KindsAlgorithmic(checkKind, synthKind) where

import Control.Monad.Except (catchError)
import Control.Monad.State.Strict (get)
import Data.Foldable (foldrM)

import Language.Granule.Checker.Kinds (inferCoeffectType)
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Primitives (closedOperation, coeffectResourceAlgebraOps, setElements, tyOps)
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Substitution

import Language.Granule.Context

import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type

import Language.Granule.Utils

checkKind :: (?globals :: Globals) =>
  Span -> Ctxt (Kind, Quantifier) -> Type -> Kind -> Checker Substitution

-- KChk_funk
checkKind s ctxt (FunTy _ t1 t2) KType = do
  subst1 <- checkKind s ctxt t1 KType
  subst2 <- checkKind s ctxt t2 KType
  combineSubstitutions s subst1 subst2

-- KChk_app
checkKind s ctxt (TyApp t1 t2) k2 = do
  (k1, subst1) <- synthKind s ctxt t2
  subst2 <- checkKind s ctxt t1 (KFun k1 k2)
  combineSubstitutions s subst1 subst2

-- KChk_opRing and KChk_effOp combined (i.e. closed operators)
checkKind s ctxt t@(TyInfix op t1 t2) k = do
  maybeSubst <- closedOperatorAtKind s ctxt op k
  case maybeSubst of
    Just subst3 -> do
      subst1 <- checkKind s ctxt t1 k
      subst2 <- checkKind s ctxt t2 k
      combineManySubstitutions s [subst1, subst2, subst3]
    Nothing -> throw OperatorUndefinedForKind { errLoc = s, errTyOp = op, errK = k }

-- KChk_coeffZero and KChk_coeffOne combined
checkKind s ctxt (TyInt n) (KPromote r) | n == 0 || n == 1 = checkKind s ctxt r KCoeffect

-- KChk_effOne
checkKind s ctxt (TyInt 1) (KPromote r) = checkKind s ctxt r KEffect

-- KChk_union
checkKind s ctxt t k@(KUnion k1 k2) =
  checkKind s ctxt t k1 `catchError` const (checkKind s ctxt t k2) `catchError` const (throw KindError { errLoc = s, errTy = t, errK = k })

-- Fall through to synthesis if checking can not be done.
checkKind s ctxt t k = do
  (k', subst) <- synthKind s ctxt t
  if k `subKind` k'
    then return subst
    else throw KindMismatch { errLoc = s, tyActualK = Just t, kExpected = k, kActual = k' }

-- | `closedOperatorAtKind` takes an operator `op` and a kind `k` and returns a
-- substitution if this is a valid operator at kind `k -> k -> k`.
closedOperatorAtKind :: (?globals :: Globals) =>
  Span -> Ctxt (Kind, Quantifier) -> TypeOperator -> Kind -> Checker (Maybe Substitution)

-- Nat case
closedOperatorAtKind _ _ op (KPromote (TyCon (internalName -> "Nat"))) =
  return $ if closedOperation op then Just [] else Nothing

-- * case
closedOperatorAtKind s ctxt TyOpTimes (KPromote t) = do
  -- See if the type is a coeffect
  (result, putChecker) <- peekChecker (checkKind s ctxt t KCoeffect)
  case result of
    Left _ -> do
      -- If not, see if the type is an effect
      (result', putChecker') <- peekChecker (checkKind s ctxt t KEffect)
      case result' of
        -- Not a closed operator at this kind
        Left  _ -> return Nothing
        -- Yes it is an effect type
        Right subst -> do
          putChecker'
          return $ Just subst
    -- Yes it is a coeffect type
    Right subst -> do
      putChecker
      return $ Just subst

-- Any other "coeffect operators" case
closedOperatorAtKind s ctxt op (KPromote t) | coeffectResourceAlgebraOps op = do
  -- See if the type is a coeffect
  (result, putChecker) <- peekChecker (checkKind s ctxt t KCoeffect)
  case result of
    Left _ -> return Nothing
    Right subst -> do
      putChecker
      return $ Just subst

closedOperatorAtKind _ _ _ _ = return Nothing

predicateOperatorAtKind :: (?globals :: Globals) =>
  Span -> Ctxt (Kind, Quantifier) -> TypeOperator -> Kind -> Checker (Maybe Substitution)
predicateOperatorAtKind s ctxt op (KPromote t) | predicateOps op = do
  (result, putChecker) <- peekChecker (checkKind s ctxt t KCoeffect)
  case result of
    Left _ -> return Nothing
    Right subst -> do
      putChecker
      return $ Just subst
predicateOperatorAtKind _ _ _ _ = return Nothing

predicateOps :: TypeOperator -> Bool
predicateOps op = (\(_, _, c) -> c) (tyOps op) == KPredicate

synthKind :: (?globals :: Globals) =>
  Span -> Ctxt (Kind, Quantifier) -> Type -> Checker (Kind, Substitution)

-- KChkS_var and KChkS_instVar
synthKind s ctxt (TyVar x) = do
  case lookup x ctxt of
    Just (k, _) -> return (k, [])
    Nothing     -> throw $ UnboundVariableError s x

-- KChkS_fun
synthKind s ctxt (FunTy _ t1 t2) = do
  subst1 <- checkKind s ctxt t1 KType
  subst2 <- checkKind s ctxt t2 KType
  subst <- combineManySubstitutions s [subst1, subst2]
  return (KType, subst)

-- KChkS_app
synthKind s ctxt (TyApp t1 t2) = do
  (funK, subst1) <- synthKind s ctxt t1
  case funK of
    (KFun k1 k2) -> do
      subst2 <- checkKind s ctxt t2 k1
      subst <- combineManySubstitutions s [subst1, subst2]
      return (k2, subst)
    _ -> throw KindError { errLoc = s, errTy = t1, errK = funK }

-- KChkS_predOp
synthKind s ctxt (TyInfix op t1 t2) | predicateOps op = do
  (k, subst1) <- synthKind s ctxt t1
  maybeSubst <- predicateOperatorAtKind s ctxt op k
  case maybeSubst of
    Just subst3 -> do
      subst2 <- checkKind s ctxt t2 k
      subst <- combineManySubstitutions s [subst1, subst2, subst3]
      return (KPredicate, subst)
    Nothing -> throw OperatorUndefinedForKind { errLoc = s, errTyOp = op, errK = k }

-- KChkS_opRing and KChkS_effOpp
synthKind s ctxt (TyInfix op t1 t2) = do
  (k, subst1) <- synthKind s ctxt t1
  maybeSubst <- closedOperatorAtKind s ctxt op k
  case maybeSubst of
    Just subst3 -> do
      subst2 <- checkKind s ctxt t2 k
      subst <- combineManySubstitutions s [subst1, subst2, subst3]
      return (k, subst)
    Nothing -> throw OperatorUndefinedForKind { errLoc = s, errTyOp = op, errK = k }

-- KChkS_effOne, KChkS_coeffZero and KChkS_coeffOne
synthKind s ctxt (TyInt n) = return (KPromote (TyCon (Id "Nat" "Nat")), [])

-- KChkS_box
synthKind s ctxt (Box c t) = do
  _ <- inferCoeffectType s c
  subst <- checkKind s ctxt t KType
  return (KType, subst)

-- KChkS_dia
synthKind s ctxt (Diamond e t) = do
  (kB, subst2) <- synthKind s ctxt e
  case kB of
    (KPromote b) -> do
      subst1 <- checkKind s ctxt b KEffect
      subst3 <- checkKind s ctxt t KType
      subst <- combineManySubstitutions s [subst1, subst2, subst3]
      return (KType, subst)
    _ -> throw KindError { errLoc = s, errTy = e, errK = kB }

-- KChkS_int and KChkS_char (and other base types)
synthKind s ctxt (TyCon id) = do
  st <- get
  case lookup id (typeConstructors st) of
      Just (kind, _, _) -> return (kind, [])
      Nothing -> do
        mConstructor <- lookupDataConstructor s id
        case mConstructor of
          Just (Forall _ [] [] t, _) -> return (KPromote t, [])
          Just _ -> error $ pretty s <> "I'm afraid I can't yet promote the polymorphic data constructor:"  <> pretty id
          Nothing -> throw UnboundTypeConstructor { errLoc = s, errId = id }

-- KChkS_set
synthKind s ctxt (TySet (t:ts)) = do
  (k, subst1) <- synthKind s ctxt t
  substs <- foldrM (\t' res -> (:res) <$> checkKind s ctxt t' k) [] ts
  subst <- combineManySubstitutions s (subst1:substs)
  case lookup k setElements of
    -- Lift this alias to the kind level
    Just t -> return (KPromote t, subst)
    Nothing ->
      -- Return a set type lifted to a kind
      case demoteKindToType k of
        Just t -> return (KPromote $ TyApp (TyCon $ mkId "Set") t, subst)
        -- If the kind cannot be demoted then we shouldn't be making a set
        Nothing -> throw KindCannotFormSet { errLoc = s,  errK = k }

synthKind _ _ t = do
  debugM "todo" (pretty t <> "\t" <> show t)
  error "TODO"

-- k1 U k2 has sub-kinds k1 and k2.
subKind :: Kind -> Kind -> Bool
subKind (KFun a b) (KFun a' b') = a `subKind` a' && b `subKind` b'
subKind (KUnion a b) (KUnion a' b') = a `subKind` a' && b `subKind` b'
subKind (KUnion a b) c = a `subKind` c || b `subKind` c
subKind a (KUnion b c) = a `subKind` b || a `subKind` c
subKind k1 k2 = k1 == k2
