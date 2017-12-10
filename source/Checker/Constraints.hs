{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}

{- Deals with compilation of coeffects into symbolic representations of SBV -}

module Checker.Constraints where

import Data.Foldable (foldrM)
import Data.SBV hiding (kindOf, name, symbolic)
import qualified Data.Set as S
import Data.List (isPrefixOf, intercalate)

import Context             (Ctxt)
import Syntax.Expr
import Syntax.Pretty

import Checker.Predicates
import Checker.Coeffects

import Debug.Trace

-- | What is the SBV represnetation of a quantifier
compileQuant :: SymWord a => Quantifier -> (String -> Symbolic (SBV a))
compileQuant ForallQ   = forall
compileQuant InstanceQ = exists
compileQuant BoundQ    = error
  "Internal bug: tried to get SBV representation of a dependent case variable"

normaliseConstraint :: Constraint -> Constraint
normaliseConstraint (Eq s c1 c2 k)   = Eq s (normalise c1) (normalise c2) k
normaliseConstraint (Leq s c1 c2 k) = Leq s (normalise c1) (normalise c2) k

-- Compile constraint into an SBV symbolic bool, along with a list of
-- constraints which are trivially unsatisfiable (e.g., things like 1=0).
compileToSBV :: Pred -> Ctxt (CKind, Quantifier) -> Ctxt CKind
             -> (Symbolic SBool, Symbolic SBool, [Constraint])
compileToSBV predicate cctxt cVarCtxt =
  (buildTheorem id compileQuant
  , buildTheorem bnot (compileQuant . flipQuant)
  , trivialUnsatisfiableConstraints predicate')

  where
    flipQuant ForallQ   = InstanceQ
    flipQuant InstanceQ = ForallQ
    flipQuant BoundQ    = BoundQ

    predicate' = rewriteConstraints cVarCtxt predicate

    buildTheorem ::
        (SBool -> SBool)
     -> (forall a. SymWord a => Quantifier -> (String -> Symbolic (SBV a)))
     -> Symbolic SBool
    buildTheorem polarity quant = do
        (pres, constraints, solverVars) <-
            foldrM (createFreshVar quant) (true, true, []) cctxt
        predC <- buildTheorem' solverVars predicate'
        return (polarity (pres ==> (constraints &&& predC)))

    -- Build the theorem, doing local creation of universal variables
    -- when needed (see Impl case)
    buildTheorem' :: Ctxt SCoeffect -> Pred -> Symbolic SBool
    buildTheorem' solverVars (Conj ps) = do
      ps' <- mapM (buildTheorem' solverVars) ps
      return $ foldr (&&&) true ps'

    buildTheorem' solverVars (Impl [] p1 p2) = do
        p1' <- buildTheorem' solverVars p1
        p2' <- buildTheorem' solverVars p2
        return $ p1' ==> p2'

    -- TODO: generalise this to not just Nat indices
    buildTheorem' solverVars (Impl (v:vs) p p') =
      forAll [v] (\vSolver -> do
         p <- buildTheorem' ((v, SNat Discrete vSolver) : solverVars) (Impl vs p p')
         return ((vSolver .>= literal 0) ==> p))

    buildTheorem' solverVars (Con cons) =
      return $ compile solverVars cons

    -- Perform a substitution on a predicate tree
    substPred rmap = predFold Conj Impl (Con . substConstraint rmap)
    substConstraint rmap (Eq s' c1 c2 k) =
        Eq s' (substCoeffect rmap c1) (substCoeffect rmap c2) k
    substConstraint rmap (Leq s' c1 c2 k) =
        Leq s' (substCoeffect rmap c1) (substCoeffect rmap c2) k

    -- Create a fresh solver variable of the right kind and
    -- with an associated refinement predicate
    createFreshVar
      :: (forall a. SymWord a => Quantifier -> (String -> Symbolic (SBV a)))
      -> (Id, (CKind, Quantifier))
      -> (SBool, SBool, Ctxt SCoeffect)
      -> Symbolic (SBool, SBool, Ctxt SCoeffect)
    -- Ignore variables coming from a dependent pattern match
    createFreshVar _ (_, (_, BoundQ)) x = return x

    createFreshVar quant
                   (var, (kind, quantifierType))
                   (universalConstraints, existentialConstraints, ctxt) = do
      (pre, symbolic) <- freshCVar quant var kind quantifierType
      let (universalConstraints', existentialConstraints') =
            case quantifierType of
              ForallQ -> (pre &&& universalConstraints, existentialConstraints)
              InstanceQ -> (universalConstraints, pre &&& existentialConstraints)
      return (universalConstraints', existentialConstraints', (var, symbolic) : ctxt)

-- given an context mapping coeffect type variables to coeffect typ,
-- then rewrite a set of constraints so that any occruences of the kind variable
-- are replaced with the coeffect type
rewriteConstraints :: Ctxt CKind -> Pred -> Pred
rewriteConstraints ctxt =
    predFold Conj Impl (\c -> Con $ foldr (uncurry updateConstraint) c ctxt)
  where
    -- `updateConstraint v k c` rewrites any occurence of the kind variable
    -- `v` in the constraint `c` with the kind `k`
    updateConstraint :: Id -> CKind -> Constraint -> Constraint
    updateConstraint ckindVar ckind (Eq s c1 c2 k) =
      Eq s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
        (case k of
          CPoly ckindVar' | ckindVar == ckindVar' -> ckind
          _ -> k)
    updateConstraint ckindVar ckind (Leq s c1 c2 k) =
      Leq s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
        (case k of
          CPoly ckindVar' | ckindVar == ckindVar' -> ckind
          _  -> k)

    -- `updateCoeffect v k c` rewrites any occurence of the kind variable
    -- `v` in the coeffect `c` with the kind `k`
    updateCoeffect :: Id -> CKind -> Coeffect -> Coeffect
    updateCoeffect ckindVar ckind (CZero (CPoly ckindVar'))
      | ckindVar == ckindVar' = CZero ckind
    updateCoeffect ckindVar ckind (COne (CPoly ckindVar'))
      | ckindVar == ckindVar' = COne ckind
    updateCoeffect ckindVar ckind (CMeet c1 c2) =
      CMeet (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CJoin c1 c2) =
      CJoin (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CPlus c1 c2) =
      CPlus (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CTimes c1 c2) =
      CTimes (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect _ _ c = c

-- Symbolic coeffects
data SCoeffect =
     SNat   NatModifier SInteger
   | SNatOmega SInteger
   | SFloat  SFloat
   | SLevel SInteger
   | SSet   (S.Set (Id, Type))
  deriving (Show, Eq)

-- | Generate a solver variable of a particular kind, along with
-- a refinement predicate
freshCVar :: (forall a . SymWord a => Quantifier -> (String -> Symbolic (SBV a)))
          -> Id -> CKind -> Quantifier -> Symbolic (SBool, SCoeffect)

freshCVar quant name (CConstr "Nat*") q = do
  solverVar <- (quant q) name
  return (solverVar .>= literal 0, SNatOmega solverVar)

freshCVar quant name (CConstr "Nat") q = do
  solverVar <- (quant q) name
  return (solverVar .>= literal 0, SNat Ordered solverVar)

-- Singleton coeffect type
freshCVar quant name (CConstr "One") q = do
  solverVar <- (quant q) name
  return (solverVar .== literal 1, SNat Ordered solverVar)

freshCVar quant name (CConstr "Nat=") q = do
  solverVar <- (quant q) name
  return (solverVar .>= literal 0, SNat Discrete solverVar)
freshCVar quant name (CConstr "Q") q = do
  solverVar <- (quant q) name
  return (true, SFloat solverVar)
freshCVar quant name (CConstr "Level") q = do
  solverVar <- (quant q) name
  return (solverVar .>= literal 0 &&& solverVar .<= 1, SLevel solverVar)
freshCVar quant _ (CConstr "Set") _ = return (true, SSet S.empty)

-- A poly typed coeffect variable whose element is 'star' gets
-- compiled into the One type (since this satisfies all the same properties)
freshCVar quant name (CPoly v) q | " star" `isPrefixOf` v
-- future TODO: resolve polymorphism to free coeffect (uninterpreted)
                           || "kprom" `isPrefixOf` v = do
  solverVar <- (quant q) name
  return (solverVar .== literal 1, SNat Ordered solverVar)

freshCVar _ _ k _ =
  error $ "Trying to make a fresh solver variable for a coeffect of kind: " ++ show k ++ " but I don't know how."

-- Compile a constraint into a symbolic bool (SBV predicate)
compile :: Ctxt SCoeffect -> Constraint -> SBool
compile vars (Eq _ c1 c2 k) =
  eqConstraint c1' c2'
    where
      c1' = compileCoeffect c1 k vars
      c2' = compileCoeffect c2 k vars
compile vars (Leq _ c1 c2 k) =
  lteConstraint c1' c2'
    where
      c1' = compileCoeffect c1 k vars
      c2' = compileCoeffect c2 k vars

-- Compile a coeffect term into its symbolic representation
compileCoeffect :: Coeffect -> CKind -> [(Id, SCoeffect)] -> SCoeffect

compileCoeffect (CSig c k) _ ctxt = compileCoeffect c k ctxt

compileCoeffect _ (CConstr "One") _
  = SNat Ordered 1

-- Any polymorphic * get's compiled to the * : One coeffec
compileCoeffect (CStar (CPoly _)) _ _ = SNat Ordered 1

compileCoeffect (Level n) (CConstr "Level") _ = SLevel . fromInteger . toInteger $ n

compileCoeffect (CNat Ordered n)  (CConstr "Nat") _
  = SNat Ordered  . fromInteger . toInteger $ n

-- This happens when we use natural number coeffects but with an
-- explicit signature to make them Nat=
compileCoeffect (CNat Ordered n)  (CConstr "Nat=") _
  = SNat Discrete . fromInteger . toInteger $ n

compileCoeffect (CNat Discrete n)  (CConstr "Nat=") _
  = SNat Discrete  . fromInteger . toInteger $ n

compileCoeffect (CNatOmega (Left ())) (CConstr "Nat*") _
  = error "TODO: Recursion not yet supported"
  -- SNatOmega . fromInteger .
  --   allElse <- forall_

compileCoeffect (CNatOmega (Right n)) (CConstr "Nat*") _
  = SNatOmega . fromInteger . toInteger $ n

compileCoeffect (CFloat r) (CConstr "Q")     _ = SFloat  . fromRational $ r
compileCoeffect (CSet xs) (CConstr "Set")   _ = SSet   . S.fromList $ xs
compileCoeffect (CVar v) _ vars =
   case lookup v vars of
    Just cvar -> cvar
    Nothing   ->
     error $ "Looking up a variable '" ++ v ++ "' in " ++ show vars

compileCoeffect c@(CMeet n m) k vars =
  case (k, compileCoeffect n k vars, compileCoeffect m k vars) of
    (CConstr "Set"  , SSet s, SSet t)      -> SSet $ S.intersection s t
    (CConstr "Level", SLevel s, SLevel t)  -> SLevel $ s `smin` t
    (CConstr "One"  , SNat _ _, SNat _ _) -> SNat Ordered 1
    (CPoly v        , SNat _ _, SNat _ _) | " start" `isPrefixOf` v
                                           -> SNat Ordered 1
    (_, SNat o1 n1, SNat o2 n2) | o1 == o2 -> SNat o1 (n1 `smin` n2)
    (_, SFloat n1, SFloat n2)              -> SFloat (n1 `smin` n2)
    _ -> error $ "Failed to compile: " ++ pretty c ++ " of kind " ++ pretty k

compileCoeffect c@(CJoin n m) k vars =
  case (k, compileCoeffect n k vars, compileCoeffect m k vars) of
    (CConstr "Set"  , SSet s, SSet t)      -> SSet $ S.intersection s t
    (CConstr "Level", SLevel s, SLevel t)  -> SLevel $ s `smax` t
    (CConstr "One"  , SNat _ _, SNat _ _) -> SNat Ordered 1
    (CPoly v        , SNat _ _, SNat _ _) | " start" `isPrefixOf` v
                                           -> SNat Ordered 1
    (_, SNat o1 n1, SNat o2 n2) | o1 == o2 -> SNat o1 (n1 `smax` n2)
    (_, SFloat n1, SFloat n2)              -> SFloat (n1 `smax` n2)
    _ -> error $ "Failed to compile: " ++ pretty c ++ " of kind " ++ pretty k

compileCoeffect c@(CPlus n m) k vars =
  case (k, compileCoeffect n k vars, compileCoeffect m k vars) of
    (CConstr "Set"  , SSet s, SSet t)           -> SSet $ S.union s t
    (CConstr "Level", SLevel lev1, SLevel lev2) -> SLevel $ lev1 `smax` lev2
    (CConstr "One"  , SNat _ _, SNat _ _)       -> SNat Ordered 1
    (CPoly v, SNat _ _, SNat _ _) | " star" `isPrefixOf` v -> SNat Ordered 1
    (_, SNat o1 n1, SNat o2 n2) | o1 == o2      -> SNat o1 (n1 + n2)
    (_, SFloat n1, SFloat n2)                   -> SFloat $ n1 + n2
    _ -> error $ "Failed to compile: " ++ pretty c ++ " of kind " ++ pretty k


compileCoeffect c@(CTimes n m) k vars =
  case (k, compileCoeffect n k vars, compileCoeffect m k vars) of
    (CConstr "Set", SSet s, SSet t)             -> SSet $ S.union s t
    (CConstr "Level", SLevel lev1, SLevel lev2) -> SLevel $ lev1 `smin` lev2
    (CConstr "One", SNat _ _, SNat _ _)         -> SNat Ordered 1
    (CPoly v, SNat _ _, SNat _ _) | " star" `isPrefixOf` v
                                                -> SNat Ordered 1
    (_, SNat o1 n1, SNat o2 n2) | o1 == o2      -> SNat o1 (n1 * n2)
    (_, SFloat n1, SFloat n2)                   -> SFloat $ n1 * n2
    _ -> error $ "Failed to compile: " ++ pretty c ++ " of kind " ++ pretty k

compileCoeffect (CZero (CConstr "Level")) (CConstr "Level") _ = SLevel 0
compileCoeffect (CZero (CConstr "Nat")) (CConstr "Nat")     _ = SNat Ordered 0
compileCoeffect (CZero (CConstr "Nat=")) (CConstr "Nat=")   _ = SNat Discrete 0
compileCoeffect (CZero (CConstr "Q"))  (CConstr "Q")        _ = SFloat (fromRational 0)
compileCoeffect (CZero (CConstr "Set")) (CConstr "Set")     _ = SSet (S.fromList [])

compileCoeffect (COne (CConstr "Level")) (CConstr "Level") _ = SLevel 1
compileCoeffect (COne (CConstr "Nat")) (CConstr "Nat")     _ = SNat Ordered 1
compileCoeffect (COne (CConstr "Nat=")) (CConstr "Nat=")   _ = SNat Discrete 1
compileCoeffect (COne (CConstr "Q")) (CConstr "Q")         _ = SFloat (fromRational 1)
compileCoeffect (COne (CConstr "Set")) (CConstr "Set")     _ = SSet (S.fromList [])

compileCoeffect _ (CPoly v) _ | " star" `isPrefixOf` v = SNat Ordered 1

-- Trying to compile a coeffect from a promotion that was never
-- constrained further: default to the singleton coeffect
-- future TODO: resolve polymorphism to free coeffect (uninterpreted)
compileCoeffect _ (CPoly v) _ | "kprom" `isPrefixOf` v = SNat Ordered 1

compileCoeffect c (CPoly _) _ =
   error $ "Trying to compile a polymorphically kinded " ++ pretty c

compileCoeffect coeff ckind _ =
   error $ "Can't compile a coeffect: " ++ pretty coeff ++ " {" ++ (show coeff) ++ "}"
        ++ " of kind " ++ pretty ckind

-- | Generate equality constraints for two symbolic coeffects
eqConstraint :: SCoeffect -> SCoeffect -> SBool
eqConstraint (SNat _ n) (SNat _ m) = n .== m
eqConstraint (SFloat n) (SFloat m)   = n .== m
eqConstraint (SLevel l) (SLevel k) = l .== k
eqConstraint x y =
   error $ "Kind error trying to generate equality " ++ show x ++ " = " ++ show y

-- | Generate less-than-equal constraints for two symbolic coeffects
lteConstraint :: SCoeffect -> SCoeffect -> SBool
lteConstraint (SNat Ordered n) (SNat Ordered m)   = n .<= m
lteConstraint (SNat Discrete n) (SNat Discrete m) = n .== m
lteConstraint (SFloat n) (SFloat m)   = n .<= m
lteConstraint (SLevel l) (SLevel k) = l .== k
lteConstraint (SSet s) (SSet t) =
  if s == t then true else false
lteConstraint x y =
   error $ "Kind error trying to generate " ++ show x ++ " <= " ++ show y


trivialUnsatisfiableConstraints :: Pred -> [Constraint]
trivialUnsatisfiableConstraints cs =
    (filter unsat) . (map normaliseConstraint) . positiveConstraints $ cs
  where
    -- Only check trivial constraints in positive positions
    -- This means we can't ever have a branch concluding false trivially
    -- TODO: do we want this really?
    positiveConstraints = predFold concat (\_ q -> q) (\x -> [x])

    unsat :: Constraint -> Bool
    unsat (Eq _ c1 c2 _)  = c1 `eqC` c2
    unsat (Leq _ c1 c2 _) = c1 `leqC` c2

    -- Attempt to see if one coeffect is trivially greater than the other
    leqC :: Coeffect -> Coeffect -> Bool
    leqC (CNat Ordered n)  (CNat Ordered m)  = not $ n <= m
    leqC (CNat Discrete n) (CNat Discrete m) = not $ n == m
    leqC (Level n) (Level m)   = not $ n <= m
    leqC (CFloat n) (CFloat m) = not $ n <= m
    leqC _ _                   = False

    -- Attempt to see if one coeffect is trivially not equal to the other
    eqC :: Coeffect -> Coeffect -> Bool
    eqC (CNat Ordered n)  (CNat Ordered m)  = n /= m
    eqC (CNat Discrete n) (CNat Discrete m) = n /= m
    eqC (Level n) (Level m)   = n /= m
    eqC (CFloat n) (CFloat m) = n /= m
    eqC _ _                   = False
