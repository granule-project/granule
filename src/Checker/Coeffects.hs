{- Deals with compilation of coeffects into symbolic representations of SBV -}

module Checker.Coeffects where

import Checker.Environment
import Context
import Syntax.Expr
import Syntax.Pretty

import Checker.Constraints (Quantifier)
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

-- What is the kind of a particular coeffect?
kindOf :: Coeffect -> MaybeT Checker CKind

-- Coeffect constants have an obvious kind
kindOf (Level _)         = return $ CConstr "Level"
kindOf (CNat Ordered _)  = return $ CConstr "Nat"
kindOf (CNat Discrete _) = return $ CConstr "Nat="
kindOf (CFloat _)         = return $ CConstr "Q"
kindOf (CSet _)          = return $ CConstr "Set"
kindOf (CNatOmega _)     = return $ CConstr "Nat*"

-- Take the join for compound coeffect epxressions
kindOf (CPlus c c')  = mguCoeffectKinds nullSpan c c'

kindOf (CTimes c c') = mguCoeffectKinds nullSpan c c'

-- Coeffect variables should have a kind in the cvar->kind environment
kindOf (CVar cvar) = do
  checkerState <- get
  case lookup cvar (ckenv checkerState) of
     Nothing -> do
       error $ "Tried to lookup kind of " ++ cvar
--       state <- get
--       let newCKind = CPoly $ "ck" ++ show (uniqueVarId state)
       -- We don't know what it is yet though, so don't update the coeffect kind env
--       put (state { uniqueVarId = uniqueVarId state + 1 })
--       return newCKind

     Just (k, _) -> return k

kindOf (CZero k) = return k
kindOf (COne k)  = return k
kindOf (CStar k)  = return k
kindOf (CSig _ k) = return k

-- This will be refined later, but for now join is the same as mgu
kindJoin :: Coeffect -> Coeffect -> MaybeT Checker CKind
kindJoin = mguCoeffectKinds nullSpan

-- Given a coeffect kind variable and a coeffect kind,
-- replace any occurence of that variable in an environment
-- and update the current solver predicate as well
updateCoeffectKind :: Id -> CKind -> MaybeT Checker ()
updateCoeffectKind ckindVar ckind = do
    checkerState <- get
    put $ checkerState
      { ckenv = rewriteEnv (ckenv checkerState),
        cVarEnv = replace (cVarEnv checkerState) ckindVar ckind }
  where
    rewriteEnv :: Env (CKind, Quantifier) -> Env (CKind, Quantifier)
    rewriteEnv [] = []
    rewriteEnv ((name, (CPoly ckindVar', q)) : env)
     | ckindVar == ckindVar' = (name, (ckind, q)) : rewriteEnv env
    rewriteEnv (x : env) = x : rewriteEnv env

-- Find the most general unifier of two coeffects
-- This is an effectful operation which can update the coeffect-kind
-- environments if a unification resolves a variable
mguCoeffectKinds :: Span -> Coeffect -> Coeffect -> MaybeT Checker CKind
mguCoeffectKinds s c1 c2 = do
  ck1 <- kindOf c1
  ck2 <- kindOf c2
  case (ck1, ck2) of
    -- Both are poly
    (CPoly kv1, CPoly kv2) -> do
      updateCoeffectKind kv1 (CPoly kv2)
      return (CPoly kv2)

   -- Left-hand side is a poly variable, but right is concrete
    (CPoly kv1, ck2') -> do
      updateCoeffectKind kv1 ck2'
      return ck2'

    -- Right-hand side is a poly variable, but left is concrete
    (ck1', CPoly kv2) -> do
      updateCoeffectKind kv2 ck1'
      return ck1'

    (CConstr k1, CConstr k2) | k1 == k2 -> return $ CConstr k1

    (CConstr "Nat=", CConstr "Nat")     -> return $ CConstr "Nat"
    (CConstr "Nat", CConstr "Nat=")     -> return $ CConstr "Nat"
    (CConstr "Nat*", CConstr "Nat")     -> return $ CConstr "Nat*"
    (CConstr "Nat", CConstr "Nat*")     -> return $ CConstr "Nat*"

    (CConstr "Nat", CConstr "Float")     -> return $ CConstr "Float"
    (CConstr "Float", CConstr "Nat")     -> return $ CConstr "Float"
    (k1, k2) -> do
      -- c2' <- renameC s (map (\(a, b) -> (b, a)) nameMap) c2
      -- c1' <- renameC s (map (\(a, b) -> (b, a)) nameMap) c1
      illTyped s $ "Cannot unify coeffect types of '" ++ pretty k1 ++ "' and '" ++ pretty k2
       ++ "' for coeffects " ++ pretty c1 ++ " and " ++ pretty c2

-- | Multiply an environment by a coeffect
--   (Derelict and promote all variables which are not discharged and are in th
--    set of used variables, (first param))
multAll :: [Id] -> Coeffect -> Env TyOrDisc -> Env TyOrDisc

multAll _ _ [] = []

multAll vars c ((name, Left t) : env) | name `elem` vars
    = (name, Right (c, t)) : multAll vars c env

multAll vars c ((name, Right (c', t)) : env) | name `elem` vars
    = (name, Right (c `CTimes` c', t)) : multAll vars c env

multAll vars c ((_, Left _) : env) = multAll vars c env
multAll vars c ((_, Right (_, _)) : env) = multAll vars c env

-- | Perform a renaming on a coeffect
renameC :: Span -> Env Id -> Coeffect -> MaybeT Checker Coeffect
renameC s rmap (CPlus c1 c2) = do
      c1' <- renameC s rmap c1
      c2' <- renameC s rmap c2
      return $ CPlus c1' c2'

renameC s rmap (CTimes c1 c2) = do
      c1' <- renameC s rmap c1
      c2' <- renameC s rmap c2
      return $ CTimes c1' c2'

renameC s rmap (CVar v) =
      case lookup v rmap of
        Just v' -> return $ CVar v'
        Nothing -> illTyped s $ "Coeffect variable " ++ v ++ " is unbound"

renameC _ _ c = return c