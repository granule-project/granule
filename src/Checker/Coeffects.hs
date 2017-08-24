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

-- The resource semiring class
class Semiring c where
  plus  :: c -> c -> c
  mult  :: c -> c -> c
  one   :: c
  zero  :: c

-- Coeffects are a semiring
instance Semiring Coeffect where
  plus c d = CPlus c d
  mult c d = CTimes c d
  one = COne
  zero = CZero

{-
oneKind :: CKind -> Coeffect
oneKind CPoly = Nat 1
oneKind CNat = Nat 1
oneKind CLevel = Level 1
-}

-- | Generate a solver variable of a particular kind, along with
-- a refinement predicate
freshCVar :: Id -> CKind -> Symbolic (SBool, SCoeffect)
freshCVar name (CConstr "Nat") = do
  solverVar <- exists name
  return (solverVar .>= literal 0, SNat solverVar)
freshCVar name (CConstr "Real") = do
  solverVar <- exists name
  return (true, SReal solverVar)
freshCVar name (CConstr "Level") = do
  solverVar <- exists name
  return (solverVar .>= literal 0 &&& solverVar .<= 1, SLevel solverVar)
freshCVar name k = do
  return (true, SAny)
--  error $ "Trying to make a fresh solver variable for a coeffect of kind: " ++ show k


eqConstraint :: SCoeffect -> SCoeffect -> SBool
eqConstraint (SNat n) (SNat m)     = n .== m
eqConstraint (SReal n) (SReal m)   = n .== m
eqConstraint (SLevel l) (SLevel k) = l .== k
eqConstraint SAny s = true
eqConstraint s SAny = true
eqConstraint x y = error $ "Trying to make equal an " ++ show x ++ " with " ++ show y

lteConstraint :: SCoeffect -> SCoeffect -> SBool
lteConstraint (SNat n) (SNat m)     = n .<= m
lteConstraint (SReal n) (SReal m)   = n .<= m
lteConstraint (SLevel l) (SLevel k) = l .<= k
lteConstraint SAny s = true
lteConstraint s SAny = true

compile :: Coeffect -> CKind -> [(Id, SCoeffect)] -> SCoeffect
compile (Level n) (CConstr "Level") _ = SLevel . fromInteger . toInteger $ n
compile (CNat n)  (CConstr "Nat")   _ = SNat   . fromInteger . toInteger $ n
compile (CReal r) (CConstr "Real")  _ = SReal  . fromRational $ r
compile (CVar v)  _ vars =
  case lookup v vars of
   Just cvar -> cvar
   Nothing   -> SAny -- error $ "Looking up a variable '" ++ v ++ "' in " ++ show vars

compile (CPlus n m) k@(CConstr "Level") vars =
  case (compile n k vars, compile m k vars) of
    (SLevel lev1, SLevel lev2) -> SLevel $ lev1 `smax` lev2

compile (CPlus n m) k vars =
  case (compile n k vars, compile m k vars) of
    (SNat n1, SNat n2) -> SNat $ n1 + n2
    (SReal n1, SReal n2) -> SReal $ n1 + n2

compile (CTimes n m) k@(CConstr "Level") vars =
  case (compile n k vars, compile m k vars) of
    (SLevel lev1, SLevel lev2) -> SLevel $ lev1 `smin` lev2
    (c, SAny)        -> c
    (SAny, c)        -> c

compile (CTimes n m) k vars =
  case (compile n k vars, compile m k vars) of
    (SNat n1, SNat n2) -> SNat $ n1 * n2
    (SReal n1, SReal n2) -> SReal $ n1 * n2

compile CZero (CConstr "Level") _ = SNat 0
compile CZero (CConstr "Nat")   _ = SNat 0
compile CZero (CConstr "Q")     _ = SReal (fromRational 0)

compile COne (CConstr "Level") _ = SNat 1
compile COne (CConstr "Nat")   _ = SNat 1
compile COne (CConstr "Q")     _ = SReal (fromRational 1)

compile _ (CPoly "")           _ = SAny
compile coeff ckind _ = error $ "Can't compile a coeffect: " ++ pretty coeff ++ " of kind " ++ show ckind

{-
-- What is the coeffect kind in this type?
tyCoeffectKind :: Type -> CKind
tyCoeffectKind (FunTy t1 t2) = tyCoeffectKind t1 `kindJoin` tyCoeffectKind t2
tyCoeffectKind (Diamond _ t) = tyCoeffectKind t
tyCoeffectKind (Box c t) = kindOf c `kindJoin` (tyCoeffectKind t)
tyCoeffectKind (ConT _) = CPoly ""
-}



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
kindOf (CNat _)     = return $ CConstr "Nat"
kindOf (CReal _)    = return $ CConstr "Real"

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
       state <- get
       let newCKind = CPoly $ "ck" ++ show (uniqueVarId state)
       -- We don't know what it is yet though, so don't update the coeffect kind env
       put (state { uniqueVarId = uniqueVarId state + 1 })
       return newCKind

-- illTyped $ "Kind unknown for coeffect variable: " ++ cvar ++ " with " ++ (show (ckenv state)) -- CPoly ""

     Just (CPoly k) ->
       case lookup k (ckkenv state) of
         Just kind -> return kind
         Nothing   -> return $ CPoly k
     Just k -> return k

-- Generic 0 and 1 get given a fresh poly kind
kindOf c | c == CZero || c == COne = do
  -- Generate a fresh coeffect kind variable
  state <- get
  let newCKind = CPoly $ "ck" ++ show (uniqueVarId state)
  -- We don't know what it is yet though, so don't update the coeffect kind env
  put (state { uniqueVarId = uniqueVarId state + 1 })
  return newCKind


-- This will be refined later, but for now join is the same as mgu
kindJoin c1 c2 = mguCoeffectKinds c1 c2

updateCoeffectVarKind :: Id -> CKind -> MaybeT Checker ()
updateCoeffectVarKind c k = do
  state <- get
  put (state { ckenv = replace (ckenv state) c k })

updateCoeffectKindVarKind :: Id -> CKind -> MaybeT Checker ()
updateCoeffectKindVarKind c k = do
  state <- get
  put (state { ckkenv = replace (ckkenv state) c k })

mguCoeffectKinds :: Coeffect -> Coeffect -> MaybeT Checker CKind
mguCoeffectKinds c1 c2 = do
  ck1 <- kindOf c1
  ck2 <- kindOf c2
  case (ck1, ck2) of
    (CPoly kv1, ck2) -> do
      updateCoeffectKindVarKind kv1 ck2
      return ck2
--      case c1 of
--        CVar cv1 -> updateCoeffectVarKind cv1 ck2
--        _        -> return ()
      return ck2
    (ck1, CPoly kv2) -> do
      updateCoeffectKindVarKind kv2 ck1
      return ck1
    (CConstr k1, CConstr k2) | k1 == k2 -> return $ CConstr k1
    (CConstr "Nat", CConstr "Real")     -> return $ CConstr "Real"
    (CConstr "Real", CConstr "Nat")     -> return $ CConstr "Real"
    (k1, k2) -> illTyped $ "Cannot unify coeffect kinds of " ++ show k1 ++ " and " ++ show k2
       ++ "\n for coeffects " ++ pretty c1 ++ " and " ++ pretty c2

-- kindJoin c d = error $ "Coeffect kind mismatch " ++ show c ++ " != " ++ show d

-- | Multiply an environment by a coeffect
--   (Derelict and promote all variables which are not discharged and are in th
--    set of used variables, (first param))
multAll :: [Id] -> Coeffect -> Env TyOrDisc -> Env TyOrDisc

multAll _ _ [] = []

multAll vars c ((id, Left t) : env) | id `elem` vars
    = (id, Right (c, t)) : multAll vars c env

multAll vars c ((id, Right (c', t)) : env) | id `elem` vars
    = (id, Right (c `mult` c', t)) : multAll vars c env

multAll vars c ((id, Left t) : env) = multAll vars c env
multAll vars c ((id, Right (_, t)) : env) = multAll vars c env
