{- Deals with compilation of coeffects into symbolic representations of SBV -}

module Checker.Coeffects where

import Checker.Environment
import Checker.Types
import Syntax.Expr
import Syntax.Pretty

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Data.Maybe (fromJust)
import Data.SBV hiding (kindOf)
import qualified Data.Set as S

import Debug.Trace

-- | Generate a solver variable of a particular kind, along with
-- a refinement predicate
freshCVar :: Id -> CKind -> Symbolic (SBool, SCoeffect)
freshCVar name (CConstr "Nat") = do
  solverVar <- exists name
  return (solverVar .>= literal 0, SNat Ordered solverVar)
freshCVar name (CConstr "Nat=") = do
  solverVar <- exists name
  return (solverVar .>= literal 0, SNat Discrete solverVar)
freshCVar name (CConstr "Real") = do
  solverVar <- exists name
  return (true, SReal solverVar)
freshCVar name (CConstr "Level") = do
  solverVar <- exists name
  return (solverVar .>= literal 0 &&& solverVar .<= 1, SLevel solverVar)
freshCVar name (CConstr "Set") = do
  return (true, SSet S.empty)
freshCVar name k = do
  error $ "Trying to make a fresh solver variable for a "
       ++ "coeffect of kind: " ++ show k ++ " but I don't know how"

-- | Generate equality constraints for two symbolic coeffects
eqConstraint :: SCoeffect -> SCoeffect -> SBool
eqConstraint (SNat _ n) (SNat _ m) = n .== m
eqConstraint (SReal n) (SReal m)   = n .== m
eqConstraint (SLevel l) (SLevel k) = l .== k
eqConstraint x y =
   error $ "Kind error trying to generate equality " ++ show x ++ " = " ++ show y

-- | Generate less-than-equal constraints for two symbolic coeffects
lteConstraint :: SCoeffect -> SCoeffect -> SBool
lteConstraint (SNat Ordered n) (SNat Ordered m)   = n .<= m
lteConstraint (SNat Discrete n) (SNat Discrete m) = n .== m
lteConstraint (SReal n) (SReal m)   = n .<= m
lteConstraint (SLevel l) (SLevel k) = l .== k
lteConstraint (SSet s) (SSet t) =
  if s == t then true else false


kindOfFromScheme :: Coeffect -> [(Id, CKind)] -> IO CKind
kindOfFromScheme c env = do
  result <- evalChecker (initState { ckenv = env }) [] (runMaybeT (kindOf c))
  case result of
    Just ckind -> return ckind
    Nothing    -> error $ "Error: Can't deduce kind for coeffect " ++ pretty c

-- What is the kind of a particular coeffect?
kindOf :: Coeffect -> MaybeT Checker CKind

-- Coeffect constants have an obvious kind
kindOf (Level _)    = return $ CConstr "Level"
kindOf (CNat Ordered _) = return $ CConstr "Nat"
kindOf (CNat Discrete _) = return $ CConstr "Nat="
kindOf (CReal _)    = return $ CConstr "Real"
kindOf (CSet _)     = return $ CConstr "Set"

-- Take the join for compound coeffect epxressions
kindOf (CPlus c c')  = do
  mguCoeffectKinds c c'

kindOf (CTimes c c') = do
  mguCoeffectKinds c c'

-- Coeffect variables should have a kind in the cvar->kind environment
kindOf (CVar cvar) = do
  state <- get
  case lookup cvar (ckenv state) of
     Nothing -> do
       error $ "Tried to lookup kind of " ++ cvar
       state <- get
       let newCKind = CPoly $ "ck" ++ show (uniqueVarId state)
       -- We don't know what it is yet though, so don't update the coeffect kind env
       put (state { uniqueVarId = uniqueVarId state + 1 })
       return newCKind

     Just k -> return k

kindOf (CZero k) = return k
kindOf (COne k)  = return k

-- This will be refined later, but for now join is the same as mgu
kindJoin c1 c2 = mguCoeffectKinds c1 c2

-- Generate a fresh coeffect variable in the solver environment
freshSolverCoeffectVar :: (Id, CKind) -> Checker ()
freshSolverCoeffectVar (cvar, kind) = Checker $ do
  checkerState <- get
  let predicate' = do
      (pred, vars) <- predicate checkerState
      case lookup cvar vars of
        Nothing -> do (refinement, solverVar) <- freshCVar cvar kind
                      return (pred &&& refinement, (cvar, solverVar) : vars)
        _ -> return (pred, vars)
  put $ checkerState { predicate = predicate' }
  return ()


-- Given a coeffect kind variable and a coeffect kind,
-- replace any occurence of that variable in an environment
updateCoeffectKindEnv :: Id -> CKind -> MaybeT Checker ()
updateCoeffectKindEnv ckindVar ckind = do
    state <- get
    put (state { ckenv = replacer (ckenv state) })
  where
    replacer :: Env CKind -> Env CKind
    replacer [] = []
    replacer ((id, CPoly ckindVar') : env)
     | ckindVar == ckindVar' = (id, ckind) : replacer env
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
    (CPoly kv1, ck2) -> do
      updateCoeffectKindEnv kv1 ck2
      -- If c1 is also a coeffect variable, then create a fresh
      -- solver variable of the correct kind
      case c1 of
        CVar cvar -> lift $ freshSolverCoeffectVar (cvar, ck2)
        _         -> return ()
      return ck2

    -- Right-hand side is a poly variable, but left is concrete
    (ck1, CPoly kv2) -> do
      updateCoeffectKindEnv kv2 ck1
      case c2 of
        CVar cvar -> lift $ freshSolverCoeffectVar (cvar, ck1)
        _         -> return ()
      return ck1

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

multAll vars c ((id, Left t) : env) | id `elem` vars
    = (id, Right (c, t)) : multAll vars c env

multAll vars c ((id, Right (c', t)) : env) | id `elem` vars
    = (id, Right (c `CTimes` c', t)) : multAll vars c env

multAll vars c ((id, Left t) : env) = multAll vars c env
multAll vars c ((id, Right (_, t)) : env) = multAll vars c env
