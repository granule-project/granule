{- Deals with compilation of coeffects into symbolic representations of SBV -}

module Checker.Coeffects where

import Checker.Types
import Syntax.Expr
import Syntax.Pretty

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


data SCoeffect =
     SNat   SInteger
   | SReal  SReal
   | SLevel SInteger
   | SAny
  deriving (Show, Eq)

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

kindOf :: Coeffect -> [(Id, CKind)] -> CKind
kindOf (Level _)    _ = CConstr "Level"
kindOf (CNat _)     _ = CConstr "Nat"
kindOf (CReal _)    _ = CConstr "Real"
kindOf (CPlus n m)  env = kindOf n env `kindJoin` kindOf m env
kindOf (CTimes n m) env = kindOf n env `kindJoin` kindOf m env
kindOf (CVar c)     env =
  case lookup c env of
     Nothing -> CPoly "" -- error $ "Kind unknown for coeffect variable: " ++ c
     Just k  -> k
kindOf CZero _ = CPoly ""
kindOf COne  _ = CPoly ""


-- This will be refined later, but for now join is the same as mgu
kindJoin c1 c2 = fromJust $ mguCoeffectKinds c1 c2

mguCoeffectKinds :: CKind -> CKind -> Maybe CKind
mguCoeffectKinds (CPoly "") c       = Just c
mguCoeffectKinds c (CPoly "")       = Just c
mguCoeffectKinds (CConstr k1) (CConstr k2) | k1 == k2 = Just $ CConstr k1
mguCoeffectKinds (CConstr "Nat") (CConstr "Real") = Just $ CConstr "Real"
mguCoeffectKinds (CConstr "Real") (CConstr "Nat") = Just $ CConstr "Real"
-- todo, not sure whether we really need this anymore
mguCoeffectKinds (CConstr "Level") _      = Just $ CConstr "Level"
mguCoeffectKinds _ (CConstr "Level")      = Just $ CConstr "Level"
mguCoeffectKinds _ _ = Nothing

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
