{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Granule.Checker.Constraints.Compile (compileTypeConstraintToConstraint, checkKind, synthKind) where

import Control.Monad.Except (catchError)
import Control.Monad.State.Strict
import Data.Foldable (foldrM)

import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Coeffects
import Language.Granule.Checker.Constraints.CompileNatKinded
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Primitives (closedOperation, coeffectResourceAlgebraOps, setElements, tyOps)
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Substitution (combineSubstitutions, combineManySubstitutions)
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Variables

import Language.Granule.Context

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Utils

compileTypeConstraintToConstraint ::
    (?globals :: Globals) => Span -> Type -> Checker Pred
compileTypeConstraintToConstraint s (TyInfix op t1 t2) = do
  k1 <- inferKindOfType s t1
  k2 <- inferKindOfType s t2
  jK <- joinKind k1 k2
  case jK of
    Just (k, _) -> do
      case demoteKindToType k of
        Just coeffTy -> compileAtType s op t1 t2 coeffTy
        _ ->  error $ pretty s <> ": I don't know how to compile at kind " <> pretty k
    Nothing ->
      case k1 of
        KVar v -> do
          st <- get
          case lookup v (tyVarContext st) of
            Just (_, ForallQ) | isGenericCoeffectExpression t2 -> compileAtType s op t1 t2 (TyVar v)
            _                                                  -> throw $ UnificationError s t1 t2
        _ -> case k2 of
              KVar v -> do
                st <- get
                case lookup v (tyVarContext st) of
                  Just (_, ForallQ) | isGenericCoeffectExpression t1 -> compileAtType s op t1 t2 (TyVar v)
                  _                                                  -> throw $ UnificationError s t1 t2
              _ -> throw $ UnificationError s t1 t2
compileTypeConstraintToConstraint s t =
  error $ pretty s <> ": I don't know how to compile a constraint `" <> pretty t <> "`"

compileAtType :: (?globals :: Globals) => Span -> TypeOperator -> Type -> Type -> Type -> Checker Pred
compileAtType s op t1 t2 coeffTy = do
  c1 <- compileNatKindedTypeToCoeffectAtType s t1 coeffTy
  c2 <- compileNatKindedTypeToCoeffectAtType s t2 coeffTy
  case op of
    TyOpEq -> return $ Con (Eq s c1 c2 coeffTy)
    TyOpNotEq -> return $ Con (Neq s c1 c2 coeffTy)
    TyOpLesser -> return $ Con (Lt s c1 c2)
    TyOpGreater -> return $ Con (Gt s c1 c2)
    TyOpLesserEq -> return $ Con (LtEq s c1 c2)
    TyOpGreaterEq -> return $ Con (GtEq s c1 c2)
    _ -> error $ pretty s <> ": I don't know how to compile binary operator " <> pretty op


--------------------------------------------------------------------------------
-- Below this point is the KindsAlgorithmic module, moved here to temporarily --
-- get around cyclic module dependencies.                                     --
--------------------------------------------------------------------------------

-- module Language.Granule.Checker.KindsAlgorithmic(checkKind, synthKind) where

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

-- KChk_set
{-checkKind s ctxt (TySet ts) k = do
  substs <- foldrM (\t res -> (:res) <$> checkKind s ctxt t k) [] ts
  combineManySubstitutions s substs-}

-- KChk_union
checkKind s ctxt t k@(KUnion k1 k2) =
  checkKind s ctxt t k1 `catchError` const (checkKind s ctxt t k2) `catchError` const (throw KindError { errLoc = s, errTy = t, errK = k })

-- Fall through to synthesis if checking can not be done.
checkKind s ctxt t k = do
  (k', subst) <- synthKind s ctxt t
  join <- k `joinKind` k'
  case join of
    Just (_, subst) -> return subst
    Nothing -> throw KindMismatch { errLoc = s, tyActualK = Just t, kExpected = k, kActual = k' }

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
  subst <- combineSubstitutions s subst1 subst2
  return (KType, subst)

-- KChkS_app
synthKind s ctxt (TyApp t1 t2) = do
  (funK, subst1) <- synthKind s ctxt t1
  case funK of
    (KFun k1 k2) -> do
      subst2 <- checkKind s ctxt t2 k1
      subst <- combineSubstitutions s subst1 subst2
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
      st <- get
      subst1 <- checkKind s (tyVarContext st) b KEffect
      subst3 <- checkKind s (tyVarContext st) t KType
      subst <- combineManySubstitutions s [subst1, subst2, subst3]
      return (KType, subst)
    _ -> throw KindError { errLoc = s, errTy = e, errK = kB }

synthKind s ctxt (TyCon (internalName -> "Pure")) = do
  -- Create a fresh type variable
  var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") KEffect
  return (KPromote $ TyVar var, [])

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

-- | `predicateOperatorAtKind` takes an operator `op` and a kind `k` and returns
-- a substitution if this is a valid operator at kind `k -> k -> KPredicate`.
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

-- | Determines if a type operator produces results of kind KPredicate.
predicateOps :: TypeOperator -> Bool
predicateOps op = (\(_, _, c) -> c) (tyOps op) == KPredicate
