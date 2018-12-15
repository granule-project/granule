{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}

{- Deals with compilation of coeffects into symbolic representations of SBV -}

module Language.Granule.Checker.Constraints where

import Data.Foldable (foldrM)
import Data.List (isPrefixOf)
import Data.SBV hiding (kindOf, name, symbolic)
import qualified Data.Set as S
import Control.Arrow (first)
import Control.Exception (assert)

import Language.Granule.Checker.Predicates
import Language.Granule.Context (Ctxt)

import Language.Granule.Checker.Constraints.SymbolicGrades
import Language.Granule.Checker.Constraints.Quantifiable
import Language.Granule.Checker.Constraints.SNatX (SNatX(..))
import qualified Language.Granule.Checker.Constraints.SNatX as SNatX

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type
import Language.Granule.Utils

-- import Debug.Trace

-- | What is the SBV represnetation of a quantifier
compileQuant :: Quantifiable a => Quantifier -> (String -> Symbolic a)
compileQuant ForallQ   = universal
compileQuant InstanceQ = existential
compileQuant BoundQ    = existential

normaliseConstraint :: Constraint -> Constraint
normaliseConstraint (Eq s c1 c2 k)   = Eq s (normalise c1) (normalise c2) k
normaliseConstraint (Neq s c1 c2 k)  = Neq s (normalise c1) (normalise c2) k
normaliseConstraint (ApproximatedBy s c1 c2 k) = ApproximatedBy s (normalise c1) (normalise c2) k

-- | Compile constraint into an SBV symbolic bool, along with a list of
-- | constraints which are trivially unequal (if such things exist) (e.g., things like 1=0).
compileToSBV :: (?globals :: Globals)
  => Pred -> Ctxt (Type, Quantifier) -> Ctxt Type
  -> (Symbolic SBool, Symbolic SBool, [Constraint])
compileToSBV predicate tyVarContext kVarContext =
  (buildTheorem id compileQuant
  , undefined -- buildTheorem bnot (compileQuant . flipQuant)
  , trivialUnsatisfiableConstraints predicate')

  where
    -- flipQuant ForallQ   = InstanceQ
    -- flipQuant InstanceQ = ForallQ
    -- flipQuant BoundQ    = BoundQ

    predicate' = rewriteConstraints kVarContext predicate

    buildTheorem ::
        (SBool -> SBool)
     -> (forall a. Quantifiable a => Quantifier -> (String -> Symbolic a))
     -> Symbolic SBool
    buildTheorem polarity quant = do
      -- Create fresh solver variables for everything in the type variable
      -- context of the write kind
        (preConstraints, constraints, solverVars) <-
            foldrM (createFreshVar quant) (true, true, []) tyVarContext

        predC <- buildTheorem' solverVars predicate'
        return (polarity (preConstraints ==> (constraints &&& predC)))

    -- Build the theorem, doing local creation of universal variables
    -- when needed (see Impl case)
    buildTheorem' :: Ctxt SGrade -> Pred -> Symbolic SBool
    buildTheorem' solverVars (Conj ps) = do
      ps' <- mapM (buildTheorem' solverVars) ps
      return $ bAnd ps'

    buildTheorem' solverVars (Impl [] p1 p2) = do
        p1' <- buildTheorem' solverVars p1
        p2' <- buildTheorem' solverVars p2
        return $ p1' ==> p2'

    -- TODO: generalise this to not just Nat indices
    buildTheorem' solverVars (Impl (v:vs) p p') =
      if v `elem` (vars p <> vars p')
        then forAll [internalName v] (\vSolver -> do
             impl <- buildTheorem' ((v, SNat vSolver) : solverVars) (Impl vs p p')
             return $ (vSolver .>= literal 0) ==> impl)
        else do
          buildTheorem' solverVars (Impl vs p p')

    buildTheorem' solverVars (Con cons) =
      return $ compile solverVars cons

    -- Perform a substitution on a predicate tree
    -- substPred rmap = predFold Conj Impl (Con . substConstraint rmap)
    -- substConstraint rmap (Eq s' c1 c2 k) =
    --     Eq s' (substCoeffect rmap c1) (substCoeffect rmap c2) k
    -- substConstraint rmap (ApproximatedBy s' c1 c2 k) =
    --     ApproximatedBy s' (substCoeffect rmap c1) (substCoeffect rmap c2) k

    -- Create a fresh solver variable of the right kind and
    -- with an associated refinement predicate
    createFreshVar
      :: (forall a. Quantifiable a => Quantifier -> (String -> Symbolic a))
      -> (Id, (Type, Quantifier))
      -> (SBool, SBool, Ctxt SGrade)
      -> Symbolic (SBool, SBool, Ctxt SGrade)
    -- Ignore variables coming from a dependent pattern match because
    -- they get created elsewhere
    createFreshVar _ (_, (_, BoundQ)) x = return x

    createFreshVar quant
                   (var, (kind, quantifierType))
                   (universalConstraints, existentialConstraints, ctxt) = do
      (pre, symbolic) <- freshCVar quant (internalName var) kind quantifierType
      let (universalConstraints', existentialConstraints') =
            case quantifierType of
              ForallQ -> (pre &&& universalConstraints, existentialConstraints)
              InstanceQ -> (universalConstraints, pre &&& existentialConstraints)
              BoundQ -> (universalConstraints, pre &&& existentialConstraints)
      return (universalConstraints', existentialConstraints', (var, symbolic) : ctxt)

-- given an context mapping coeffect type variables to coeffect typ,
-- then rewrite a set of constraints so that any occruences of the kind variable
-- are replaced with the coeffect type
rewriteConstraints :: Ctxt Type -> Pred -> Pred
rewriteConstraints ctxt =
    predFold Conj Impl (\c -> Con $ foldr (uncurry updateConstraint) c ctxt)
  where
    -- `updateConstraint v k c` rewrites any occurence of the kind variable
    -- `v` in the constraint `c` with the kind `k`
    updateConstraint :: Id -> Type -> Constraint -> Constraint
    updateConstraint ckindVar ckind (Eq s c1 c2 k) =
      Eq s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
        (case k of
          TyVar ckindVar' | ckindVar == ckindVar' -> ckind
          _ -> k)
    updateConstraint ckindVar ckind (Neq s c1 c2 k) =
            Neq s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
              (case k of
                TyVar ckindVar' | ckindVar == ckindVar' -> ckind
                _ -> k)

    updateConstraint ckindVar ckind (ApproximatedBy s c1 c2 k) =
      ApproximatedBy s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
        (case k of
          TyVar ckindVar' | ckindVar == ckindVar' -> ckind
          _  -> k)

    -- `updateCoeffect v k c` rewrites any occurence of the kind variable
    -- `v` in the coeffect `c` with the kind `k`
    updateCoeffect :: Id -> Type -> Coeffect -> Coeffect
    updateCoeffect ckindVar ckind (CZero (TyVar ckindVar'))
      | ckindVar == ckindVar' = CZero ckind
    updateCoeffect ckindVar ckind (COne (TyVar ckindVar'))
      | ckindVar == ckindVar' = COne ckind
    updateCoeffect ckindVar ckind (CMeet c1 c2) =
      CMeet (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CJoin c1 c2) =
      CJoin (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CPlus c1 c2) =
      CPlus (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CTimes c1 c2) =
      CTimes (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CExpon c1 c2) =
      CExpon (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CInterval c1 c2) =
      CInterval (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect _ _ c = c


-- | Symbolic coeffect representing 0..Inf
zeroToInfinity = SInterval (SExtNat $ SNatX 0) (SExtNat SNatX.inf)

-- | Generate a solver variable of a particular kind, along with
-- a refinement predicate
freshCVar :: (forall a . Quantifiable a => Quantifier -> (String -> Symbolic a))
          -> String -> Type -> Quantifier -> Symbolic (SBool, SGrade)

freshCVar quant name (isInterval -> Just t) q = do
  -- Interval, therefore recursively generate fresh vars for the lower and upper
  (predLb, solverVarLb) <- freshCVar quant (name <> ".lower") t q
  (predUb, solverVarUb) <- freshCVar quant (name <> ".upper") t q
  return
     -- Respect the meaning of intervals
    ( predLb &&& predUb &&& solverVarUb .>= solverVarLb
    , SInterval solverVarLb solverVarUb
    )

freshCVar quant name (TyCon k) q = do
  case internalName k of
    -- Floats (rationals)
    "Q" -> do
      solverVar <- quant q name
      return (true, SFloat solverVar)

    -- Esssentially a stub for sets at this point
    "Set"       -> return (true, SSet S.empty)

    _ -> do -- Otherwise it must be an SInteger-like constraint:
      solverVar <- quant q name
      case internalName k of
        "Nat"       -> return (solverVar .>= 0, SNat solverVar)
        "Level"     -> return (solverVar .== 0 ||| solverVar .== 1, SLevel solverVar)

-- Extended nat
freshCVar quant name t q | t == extendedNat = do
  solverVar <- quant q name
  return (SNatX.representationConstraint $ SNatX.xVal solverVar
        , SExtNat solverVar)

-- A poly typed coeffect variable compiled into the
--  infinity value (since this satisfies all the semiring properties on the nose)
freshCVar quant name (TyVar v) q | "kprom" `isPrefixOf` internalName v = do
-- future TODO: resolve polymorphism to free coeffect (uninterpreted)
-- TODO: possibly this can now be removed
  return (true, SPoint)

freshCVar _ _ t _ =
  error $ "Trying to make a fresh solver variable for a grade of type: "
   <> show t <> " but I don't know how."

-- Compile a constraint into a symbolic bool (SBV predicate)
compile :: (?globals :: Globals) =>
  Ctxt SGrade -> Constraint -> SBool
compile vars (Eq _ c1 c2 k) =
  eqConstraint c1' c2'
    where
      c1' = compileCoeffect c1 k vars
      c2' = compileCoeffect c2 k vars
compile vars (Neq _ c1 c2 k) =
   bnot (eqConstraint c1' c2')
  where
    c1' = compileCoeffect c1 k vars
    c2' = compileCoeffect c2 k vars
compile vars (ApproximatedBy _ c1 c2 k) = -- trace (show c1 <> "\n" <> show c2 <> "\n" <> show k)
  approximatedByOrEqualConstraint c1' c2'
    where
      c1' = compileCoeffect c1 k vars
      c2' = compileCoeffect c2 k vars

-- | Compile a coeffect term into its symbolic representation
compileCoeffect :: (?globals :: Globals) =>
  Coeffect -> Type -> [(Id, SGrade)] -> SGrade

compileCoeffect (CSig c k) _ ctxt = compileCoeffect c k ctxt

compileCoeffect (Level n) (TyCon k) _ | internalName k == "Level" =
  SLevel . fromInteger . toInteger $ n

-- Any polymorphic `Inf` gets compiled to the `Inf : [0..inf]` coeffect
-- TODO: see if we can erase this, does it actually happen anymore?
compileCoeffect (CInfinity (Just (TyVar _))) _ _ = zeroToInfinity
compileCoeffect (CInfinity Nothing) _ _ = zeroToInfinity
compileCoeffect (CInfinity _) t _
  | t == extendedNat = SExtNat SNatX.inf
compileCoeffect (CNat n) k _ | k == nat =
  SNat  . fromInteger . toInteger $ n

compileCoeffect (CNat n) k _ | k == extendedNat =
  SExtNat . fromInteger . toInteger $ n

compileCoeffect (CFloat r) (TyCon k) _ | internalName k == "Q" =
  SFloat  . fromRational $ r

compileCoeffect (CSet xs) (TyCon k) _ | internalName k == "Set" =
  SSet . S.fromList $ map (first mkId) xs

compileCoeffect (CVar v) _ vars =
   case lookup v vars of
    Just cvar -> cvar
    _ -> error $ "Looking up a variable '" <> pretty v <> "' in " <> show vars

compileCoeffect c@(CMeet n m) k vars =
  (compileCoeffect n k vars) `symGradeMeet` (compileCoeffect m k vars)

compileCoeffect c@(CJoin n m) k vars =
  (compileCoeffect n k vars) `symGradeJoin` (compileCoeffect m k vars)

compileCoeffect c@(CPlus n m) k vars =
  (compileCoeffect n k vars) `symGradePlus` (compileCoeffect m k vars)

compileCoeffect c@(CTimes n m) k vars =
  (compileCoeffect n k vars) `symGradeTimes` (compileCoeffect m k vars)

compileCoeffect c@(CExpon n m) k vars =
  case (compileCoeffect n k vars, compileCoeffect m k vars) of
    (SNat n1, SNat n2) -> SNat (n1 .^ n2)
    _ -> error $ "Failed to compile: " <> pretty c <> " of kind " <> pretty k

compileCoeffect c@(CInterval lb ub) (isInterval -> Just t) vars =
  SInterval (compileCoeffect lb t vars) (compileCoeffect ub t vars)

compileCoeffect (CZero k') k vars  =
  case (k', k) of
    (TyCon k', TyCon k) -> assert (internalName k' == internalName k) $
      case internalName k' of
        "Level"     -> SLevel 0
        "Nat"       -> SNat 0
        "Q"         -> SFloat (fromRational 0)
        "Set"       -> SSet (S.fromList [])
    (otherK', otherK) | (otherK' == extendedNat || otherK' == nat) && otherK == extendedNat ->
      SExtNat 0
    -- Build an interval for 0
    (isInterval -> Just t, isInterval -> Just t') ->
      SInterval
        (compileCoeffect (CZero t) t' vars)
        (compileCoeffect (CZero t) t' vars)

compileCoeffect (COne k') k vars =
  case (k', k) of
    (TyCon k', TyCon k) -> assert (internalName k' == internalName k) $
      case internalName k' of
        "Level"     -> SLevel 1
        "Nat"       -> SNat 1
        "Q"         -> SFloat (fromRational 1)
        "Set"       -> SSet (S.fromList [])
    (otherK', otherK) | (otherK' == extendedNat || otherK' == nat) && otherK == extendedNat ->
      SExtNat 1
    -- Build an interval for 1
    (isInterval -> Just t, isInterval -> Just t') ->
        SInterval
          (compileCoeffect (COne t) t' vars)
          (compileCoeffect (COne t) t' vars)

-- Trying to compile a coeffect from a promotion that was never
-- constrained further: default to the cartesian coeffect
-- future TODO: resolve polymorphism to free coeffect (uninterpreted)
compileCoeffect c (TyVar v) _ | "kprom" `isPrefixOf` internalName v = SPoint

compileCoeffect c (TyVar _) _ =
   error $ "Trying to compile a polymorphically kinded " <> pretty c

compileCoeffect coeff ckind _ =
   error $ "Can't compile a coeffect: " <> pretty coeff <> " {" <> (show coeff) <> "}"
        <> " of kind " <> pretty ckind

-- | Generate equality constraints for two symbolic coeffects
eqConstraint :: SGrade -> SGrade -> SBool
eqConstraint (SNat n) (SNat m) = n .== m
eqConstraint (SFloat n) (SFloat m) = n .== m
eqConstraint (SLevel l) (SLevel k) = l .== k
eqConstraint (SInterval lb1 ub1) (SInterval lb2 ub2) =
  (eqConstraint lb1 lb2) &&& (eqConstraint ub1 ub2)
eqConstraint (SExtNat x) (SExtNat y) = x .== y
eqConstraint SPoint SPoint = true
eqConstraint x y =
   error $ "Kind error trying to generate equality " <> show x <> " = " <> show y

-- | Generate less-than-equal constraints for two symbolic coeffects
approximatedByOrEqualConstraint :: SGrade -> SGrade -> SBool
approximatedByOrEqualConstraint (SNat n) (SNat m) = n .== m
approximatedByOrEqualConstraint (SFloat n) (SFloat m)   = n .<= m
approximatedByOrEqualConstraint (SLevel l) (SLevel k) = l .>= k
approximatedByOrEqualConstraint (SSet s) (SSet t) =
  if s == t then true else false
approximatedByOrEqualConstraint SPoint SPoint = true

-- Perform approximation when nat-like grades are involved
approximatedByOrEqualConstraint
    (SInterval (natLike -> Just lb1) (natLike -> Just ub1))
    (SInterval (natLike -> Just lb2) (natLike -> Just ub2)) =
      (lb2 .<= lb1) &&& (ub1 .<= ub2)

-- if intervals are not nat-like then use the notion of approximation
-- given here
approximatedByOrEqualConstraint (SInterval lb1 ub1) (SInterval lb2 ub2) =
  (approximatedByOrEqualConstraint lb2 lb1)
  &&& (approximatedByOrEqualConstraint ub1 ub2)

approximatedByOrEqualConstraint (SExtNat x) (SExtNat y) = x .== y
approximatedByOrEqualConstraint x y =
   error $ "Kind error trying to generate " <> show x <> " <= " <> show y


trivialUnsatisfiableConstraints :: Pred -> [Constraint]
trivialUnsatisfiableConstraints cs =
    (filter unsat) . (map normaliseConstraint) . positiveConstraints $ cs
  where
    -- Only check trivial constraints in positive positions
    -- This means we don't report a branch concluding false trivially
    -- TODO: may check trivial constraints everywhere?
    positiveConstraints = predFold concat (\_ _ q -> q) (\x -> [x])

    unsat :: Constraint -> Bool
    unsat (Eq _ c1 c2 _)  = c1 `neqC` c2
    unsat (Neq _ c1 c2 _) = not (c1 `neqC` c2)
    unsat (ApproximatedBy _ c1 c2 _) = c1 `approximatedByC` c2

    -- TODO: unify this with eqConstraint and approximatedByOrEqualConstraint
    -- Attempt to see if one coeffect is trivially greater than the other
    approximatedByC :: Coeffect -> Coeffect -> Bool
    approximatedByC (CNat n) (CNat m) = not $ n == m
    approximatedByC (Level n) (Level m)   = not $ n >= m
    approximatedByC (CFloat n) (CFloat m) = not $ n <= m
    approximatedByC (CInterval lb1 ub1) (CInterval lb2 ub2) =
        not $ (approximatedByC lb2 lb1) && (approximatedByC ub1 ub2)
    approximatedByC _ _                   = False

    -- Attempt to see if one coeffect is trivially not equal to the other
    neqC :: Coeffect -> Coeffect -> Bool
    neqC (CNat n) (CNat m) = n /= m
    neqC (Level n) (Level m)   = n /= m
    neqC (CFloat n) (CFloat m) = n /= m
    neqC (CInterval lb1 ub1) (CInterval lb2 ub2) =
      neqC lb1 lb2 || neqC ub1 ub2
    neqC _ _                   = False
