{- Deals with compilation of coeffects into symbolic representations of SBV -}

module Checker.Coeffects where

import Checker.Environment
import Checker.Types
import Context
import Syntax.Expr
import Syntax.Pretty

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe



kindOfFromScheme :: Coeffect -> [(Id, CKind)] -> IO CKind
kindOfFromScheme c env = do
  result <- evalChecker (initState { ckenv = env }) [] (runMaybeT (kindOf c))
  case result of
    Just ckind -> return ckind
    Nothing    -> error $ "Error: Can't deduce kind for coeffect " ++ pretty c

-- What is the kind of a particular coeffect?
kindOf :: Coeffect -> MaybeT Checker CKind

-- Coeffect constants have an obvious kind
kindOf (Level _)         = return $ CConstr "Level"
kindOf (CNat Ordered _)  = return $ CConstr "Nat"
kindOf (CNat Discrete _) = return $ CConstr "Nat="
kindOf (CReal _)         = return $ CConstr "Q"
kindOf (CSet _)          = return $ CConstr "Set"
kindOf (CNatOmega _)     = undefined

-- Take the join for compound coeffect epxressions
kindOf (CPlus c c')  = mguCoeffectKinds c c'

kindOf (CTimes c c') = mguCoeffectKinds c c'

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

     Just k -> return k

kindOf (CZero k) = return k
kindOf (COne k)  = return k

-- This will be refined later, but for now join is the same as mgu
kindJoin :: Coeffect -> Coeffect -> MaybeT Checker CKind
kindJoin = mguCoeffectKinds



-- Given a coeffect kind variable and a coeffect kind,
-- replace any occurence of that variable in an environment
updateCoeffectKindEnv :: Id -> CKind -> MaybeT Checker ()
updateCoeffectKindEnv ckindVar ckind = do
    checkerState <- get
    put $ checkerState { ckenv = replacer (ckenv checkerState) }
  where
    replacer :: Env CKind -> Env CKind
    replacer [] = []
    replacer ((name, CPoly ckindVar') : env)
     | ckindVar == ckindVar' = (name, ckind) : replacer env
    replacer (x : env) = x : replacer env

-- Find the most general unifier of two coeffects
-- This is an effectful operation which can update the coeffect-kind
-- environments if a unification resolves a variable
mguCoeffectKinds :: Coeffect -> Coeffect -> MaybeT Checker CKind
mguCoeffectKinds c1 c2 = do
  ck1 <- kindOf c1
  ck2 <- kindOf c2
  case (ck1, ck2) of
    -- Both are poly
    (CPoly kv1, CPoly kv2) -> do
      updateCoeffectKindEnv kv1 (CPoly kv2)
      return (CPoly kv2)

   -- Left-hand side is a poly variable, but right is concrete
    (CPoly kv1, ck2') -> do
      updateCoeffectKindEnv kv1 ck2'
      return ck2'

    -- Right-hand side is a poly variable, but left is concrete
    (ck1', CPoly kv2) -> do
      updateCoeffectKindEnv kv2 ck1'
      return ck1'

    (CConstr k1, CConstr k2) | k1 == k2 -> return $ CConstr k1

    (CConstr "Nat=", CConstr "Nat")     -> return $ CConstr "Nat"
    (CConstr "Nat", CConstr "Nat=")     -> return $ CConstr "Nat"

    (CConstr "Nat", CConstr "Real")     -> return $ CConstr "Real"
    (CConstr "Real", CConstr "Nat")     -> return $ CConstr "Real"
    (k1, k2) -> illTyped $ "Cannot unify coeffect kinds of " ++ pretty k1 ++ " and " ++ pretty k2
       ++ "for coeffects " ++ pretty c1 ++ " and " ++ pretty c2

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
