module Language.Granule.Checker.KindsAlgorithmic where

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
    Span -> Ctxt Kind -> Type -> Kind -> Checker Substitution

checkKind s ctxt (FunTy t1 t2) KType = do
    subst1 <- checkKind s ctxt t1 KType
    subst2 <- checkKind s ctxt t2 KType
    combineSubstitutions s subst1 subst2

checkKind s ctxt (TyApp t1 t2) k2 = do
    (k1, subst1) <- synthKind s ctxt t2
    subst2 <- checkKind s ctxt t1 (KFun k1 k2)
    combineSubstitutions s subst1 subst2

checkKind s ctxt (TyInfix op t1 t2) k = do
    isClosedAndSubst <- closedOperatorAtKind s ctxt op k
    case isClosedAndSubst of
        (True, subst) -> do
            subst1 <- checkKind s ctxt t1 k
            subst2 <- checkKind s ctxt t2 k
            combineManySubstitutions s [subst, subst1, subst2]
            
        (False, _) ->
            throw $ OperatorUndefinedForKind { errLoc = s, errTyOp = op, errK = k }

checkKind s ctxt _ k = undefined

closedOperatorAtKind :: (?globals :: Globals) =>
    Span -> Ctxt Kind -> TypeOperator -> Kind -> Checker (Bool, Substitution)

closedOperatorAtKind _ _ op (KPromote (TyCon (internalName -> "Nat"))) =
    return (closedOperation op, [])

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

closedOperatorAtKind s ctxt op (KPromote t) | coeffectResourceAlgebraOps op = do
    -- See if the type is a coeffect
    (result, putChecker) <- peekChecker (checkKind s ctxt t KCoeffect)
    case result of
        Left _ -> return (False, [])
        Right subst -> do
            putChecker
            return (True, subst)

closedOperatorAtKind _ _ _ _ = return (False, [])


synthKind :: -- (?globals :: Globals) =>
    Span -> Ctxt Kind -> Type -> Checker (Kind, Substitution)
synthKind = undefined