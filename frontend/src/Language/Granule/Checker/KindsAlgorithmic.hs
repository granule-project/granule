{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

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

checkKind :: (?globals :: Globals, HasLevel l) =>
    Span -> Ctxt (TypeWithLevel, Quantifier) -> Type l -> Type (Succ l) -> Checker Substitution

-- KChk_Funk
checkKind s ctxt (FunTy _ t1 t2) (Type l) = do
    subst1 <- checkKind s ctxt t1 (Type l)
    subst2 <- checkKind s ctxt t2 (Type l)
    combineSubstitutions s subst1 subst2

-- KChk_App
checkKind s ctxt (TyApp t1 t2) k2 = do
    (k1, subst1) <- synthKind s ctxt t2
    subst2 <- checkKind s ctxt t1 (FunTy Nothing k1 k2)
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
            undefined -- throw $ OperatorUndefinedForKind { errLoc = s, errTyOp = op, errK = k }

-- TODO
checkKind s ctxt _ k = undefined

-- | `closedOperatorAtKind` takes an operator `op` and a kind `k` and returns true
-- if this is a valid operator at kind `k -> k -> k`
closedOperatorAtKind :: (?globals :: Globals, HasLevel l) =>
    Span -> Ctxt (TypeWithLevel, Quantifier) -> TypeOperator -> Type l -> Checker (Bool, Substitution)

-- Nat case
closedOperatorAtKind _ _ op (TyCon (internalName -> "Nat")) =
    return (closedOperation op, [])

-- * case
closedOperatorAtKind s ctxt TyOpTimes t = do
    -- See if the type is a coeffect
    (result, putChecker) <- peekChecker (checkKind s ctxt t (tyCon "Coeffect"))
    case result of
        Left _ -> do
            -- If not, see if the type is an effect
            (result', putChecker') <- peekChecker (checkKind s ctxt t (tyCon "Effect"))
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
closedOperatorAtKind s ctxt op t | coeffectResourceAlgebraOps op = do
    -- See if the type is a coeffect
    (result, putChecker) <- peekChecker (checkKind s ctxt t (tyCon "Coeffect"))
    case result of
        Left _ -> return (False, [])
        Right subst -> do
            putChecker
            return (True, subst)

closedOperatorAtKind _ _ _ _ = return (False, [])

-- TODO
synthKind :: forall l . HasLevel l => -- (?globals :: Globals) =>
    Span -> Ctxt (TypeWithLevel, Quantifier) -> Type l -> Checker (Type (Succ l), Substitution)

-- KChkS_var and KChkS instVar
synthKind s ctxt t@(TyVar x) = do
  case lookup x ctxt of
    Just (tl@(TypeWithLevel l k), _) ->
      case isAtLevel l k (LSucc (getLevel t)) of
        Just k' -> return (k', [])
        Nothing -> throw $ WrongLevel s tl (IsLevel $ getLevel' (LevelProxy :: LevelProxy l))
    Nothing     -> throw $ UnboundVariableError s x

synthKind s ctxt t = error "TODO"