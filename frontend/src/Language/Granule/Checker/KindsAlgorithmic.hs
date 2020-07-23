module Language.Granule.Checker.KindsAlgorithmic(checkKind, synthKind) where

import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Monad
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.Primitives (closedOperation, coeffectResourceAlgebraOps, tyOps)

import Language.Granule.Context

import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Identifiers
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

-- KChk_opPred
checkKind s ctxt t@(TyInfix op t1 t2) KPredicate = do
  (argK, subst1) <- synthKind s ctxt t1
  maybeSubst <- predicateOperatorAtKind s ctxt op argK
  case maybeSubst of
    Just subst3 -> do
      subst2 <- checkKind s ctxt t2 argK
      combineManySubstitutions s [subst1, subst2, subst3]
    Nothing -> throw OperatorUndefinedForKind { errLoc = s, errTyOp = op, errK = argK }

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

-- Fall through to synthesis if checking can not be done.
checkKind s ctxt t k = do
  (k', subst) <- synthKind s ctxt t
  if k == k'
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

synthKind :: -- (?globals :: Globals) =>
  Span -> Ctxt (Kind, Quantifier) -> Type -> Checker (Kind, Substitution)

-- KChkS_var and KChkS_instVar
synthKind s ctxt (TyVar x) = do
  case lookup x ctxt of
    Just (k, _) -> return (k, [])
    Nothing     -> throw $ UnboundVariableError s x

-- KChkS_Int and KChkS_Char
--synthKind s ctxt (TyCon id) | isBaseType id = return (KType, [])

synthKind s ctxt t = error "TODO"

{-isBaseType :: Id -> Checker Bool
isBaseType = do
  st <- get
  case lookup id (typeConstructors st) of
    Just (KType, _, _) -> return True
    _ -> return False-}