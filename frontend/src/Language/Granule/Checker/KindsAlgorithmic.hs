module Language.Granule.Checker.KindsAlgorithmic where

import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Monad
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.Primitives (closedOperation, coeffectResourceAlgebraOps)
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Context

import Language.Granule.Utils

checkKind :: (?globals :: Globals) =>
    Span -> Ctxt (Kind, Quantifier) -> Type -> Kind -> Checker Substitution

-- KChk_Funk
checkKind s ctxt (FunTy _ t1 t2) KType = do
    subst1 <- checkKind s ctxt t1 KType
    subst2 <- checkKind s ctxt t2 KType
    combineSubstitutions s subst1 subst2

-- KChk_App
checkKind s ctxt (TyApp t1 t2) k2 = do
    (k1, subst1) <- synthKind s ctxt t2
    subst2 <- checkKind s ctxt t1 (KFun k1 k2)
    combineSubstitutions s subst1 subst2

-- KChk_opRing and KChk_effOp combined
checkKind s ctxt (TyInfix op t1 t2) k = do
    isClosedAndSubst <- closedOperatorAtKind s ctxt op k
    case isClosedAndSubst of
        (True, subst) -> do
            subst1 <- checkKind s ctxt t1 k
            subst2 <- checkKind s ctxt t2 k
            combineManySubstitutions s [subst, subst1, subst2]

        (False, _) ->
            throw $ OperatorUndefinedForKind { errLoc = s, errTyOp = op, errK = k }

-- TODO
checkKind s ctxt _ k = undefined

-- | `closedOperatorAtKind` takes an operator `op` and a kind `k` and returns true
-- if this is a valid operator at kind `k -> k -> k`
closedOperatorAtKind :: (?globals :: Globals) =>
    Span -> Ctxt (Kind, Quantifier) -> TypeOperator -> Kind -> Checker (Bool, Substitution)

-- Nat case
closedOperatorAtKind _ _ op (KPromote (TyCon (internalName -> "Nat"))) =
    return (closedOperation op, [])

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
                Left  _ -> return (False, [])
                -- Yes it is an effect type
                Right subst -> do
                    putChecker'
                    return (True, subst)
        -- Yes it is a coeffect type
        Right subst -> do
            putChecker
            return (True, subst)

-- Any other "coeffect operators" case
closedOperatorAtKind s ctxt op (KPromote t) | coeffectResourceAlgebraOps op = do
    -- See if the type is a coeffect
    (result, putChecker) <- peekChecker (checkKind s ctxt t KCoeffect)
    case result of
        Left _ -> return (False, [])
        Right subst -> do
            putChecker
            return (True, subst)

closedOperatorAtKind _ _ _ _ = return (False, [])

-- TODO
synthKind :: -- (?globals :: Globals) =>
    Span -> Ctxt (Kind, Quantifier) -> Type -> Checker (Kind, Substitution)

-- KChkS_var and KChkS instVar
synthKind s ctxt (TyVar x) = do
  case lookup x ctxt of
    Just (k, _) -> return (k, [])
    Nothing     -> throw $ UnboundVariableError s x

synthKind s ctxt t = error "TODO"