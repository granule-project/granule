{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}


{- Deals with compilation of coeffects into symbolic representations of SBV -}

module Language.Granule.Checker.Constraints where

--import Data.Foldable (foldrM)
import Data.SBV hiding (kindOf, name, symbolic)
import qualified Data.Set as S
import Control.Arrow (first)
import Control.Exception (assert)
import Control.Monad (liftM2)

import Language.Granule.Checker.Predicates
import Language.Granule.Context (Ctxt)

import Language.Granule.Checker.Constraints.SymbolicGrades
import qualified Language.Granule.Checker.Constraints.SNatX as SNatX

import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type
import Language.Granule.Utils

-- | Compile constraint into an SBV symbolic bool, along with a list of
-- | constraints which are trivially unequal (if such things exist) (e.g., things like 1=0).
compileToSBV :: (?globals :: Globals)
  => Pred
  -> (Symbolic SBool, Symbolic SBool, [Constraint])
compileToSBV predicate =
  (symbolicTheorem predicate
  , undefined -- buildTheorem sNot (compileQuant . flipQuant)
  , trivialUnsatisfiableConstraints predicate)

  where
    -- flipQuant ForallQ   = InstanceQ
    -- flipQuant InstanceQ = ForallQ
    -- flipQuant BoundQ    = BoundQ

    symbolicTheorem = buildTheorem' []

    -- Build the theorem, doing local creation of variables
    -- when needed
    buildTheorem' :: Ctxt SGrade -> Pred -> Symbolic SBool
    buildTheorem' solverVars (Conj ps) = do
      ps' <- mapM (buildTheorem' solverVars) ps
      return $ sAnd ps'

    buildTheorem' solverVars (Disj ps) = do
      ps' <- mapM (buildTheorem' solverVars) ps
      return $ sOr ps'

    buildTheorem' solverVars (Impl p1 p2) = do
        p1' <- buildTheorem' solverVars p1
        p2' <- buildTheorem' solverVars p2
        return $ p1' .=> p2'

    buildTheorem' solverVars (NegPred p) = do
        p' <- buildTheorem' solverVars p
        return $ sNot p'

    buildTheorem' solverVars (Exists v k p) =
      if v `elem` (freeVars p)
        then
          case demoteKindToType k of
            Just t ->
              freshCVarScoped compileQuantScoped (internalName v) t InstanceQ
                (\(varPred, solverVar) -> do
                  pred' <- buildTheorem' ((v, solverVar) : solverVars) p
                  return (varPred .&& pred'))

            Nothing ->
              solverError $ "Trying to make a fresh existential solver variable for a grade of kind: "
                             <> show k <> " but I don't know how."
        else
          -- optimisation, if a variable does not appear free
          buildTheorem' solverVars p

    buildTheorem' solverVars (Forall v k p) =
      if v `elem` (freeVars p)
        then
          case demoteKindToType k of
            Just t ->
              freshCVarScoped compileQuantScoped (internalName v) t ForallQ
                (\(varPred, solverVar) -> do
                  pred' <- buildTheorem' ((v, solverVar) : solverVars) p
                  return (varPred .=> pred'))

            Nothing ->
              solverError $ "Trying to make a fresh universal solver variable for a grade of kind: "
                             <> show k <> " but I don't know how."
        else
          -- optimisation, if a variable does not appear free
          buildTheorem' solverVars p

    buildTheorem' solverVars (Con cons) =
      compile solverVars cons

-- | Symbolic coeffect representing 0..Inf
zeroToInfinity :: SGrade
zeroToInfinity = SInterval (SExtNat $ SNatX.SNatX 0) (SExtNat SNatX.inf)

freshCVarScoped ::
    (forall a . QuantifiableScoped a => Quantifier -> String -> (SBV a -> Symbolic SBool) -> Symbolic SBool)
  -> String
  -> Type
  -> Quantifier
  -> ((SBool, SGrade) -> Symbolic SBool)
  -> Symbolic SBool
freshCVarScoped quant name (isInterval -> Just t) q k =

  freshCVarScoped quant (name <> ".lower") t q
   (\(predLb, solverVarLb) ->
      freshCVarScoped quant (name <> ".upper") t q
       (\(predUb, solverVarUb) -> do
          -- Respect the meaning of intervals
          lessEq <- symGradeLessEq solverVarLb solverVarUb
          k ( predLb .&& predUb .&& lessEq
            , SInterval solverVarLb solverVarUb )
          ))

freshCVarScoped quant name (isProduct -> Just (t1, t2)) q k =

  freshCVarScoped quant (name <> ".fst") t1 q
    (\(predFst, solverVarFst) ->
      freshCVarScoped quant (name <> ".snd") t2 q
        (\(predSnd, solverVarSnd) ->
          k (predFst .&& predSnd, SProduct solverVarFst solverVarSnd)))

freshCVarScoped quant name (TyCon (internalName -> "Q")) q k =
  -- Floats (rationals)
    quant q name (\solverVar -> k (sTrue, SFloat solverVar))

freshCVarScoped quant name (TyCon conName) q k =
    -- Integer based
    quant q name (\solverVar ->
      case internalName conName of
        "Nat"    -> k (solverVar .>= 0, SNat solverVar)
        "Level"  -> k (solverVar .== literal privateRepresentation
                  .|| solverVar .== literal publicRepresentation
                  .|| solverVar .== literal unusedRepresentation
                    , SLevel solverVar)
        "OOZ"    -> k (solverVar .== 0 .|| solverVar .== 1, SOOZ (ite (solverVar .== 0) sFalse sTrue))
        k -> solverError $ "I don't know how to make a fresh solver variable of type " <> show conName)

freshCVarScoped quant name t q k | t == extendedNat = do
   quant q name (\solverVar ->
    k (SNatX.representationConstraint solverVar
     , SExtNat (SNatX.SNatX solverVar)))

freshCVarScoped quant name (TyVar v) q k =
  quant q name (\solverVar -> k (sTrue, SUnknown $ SynLeaf $ Just solverVar))

freshCVarScoped _ _ t _ _ =
  solverError $ "Trying to make a fresh solver variable for a grade of type: "
      <> show t <> " but I don't know how."

-- | What is the SBV representation of a quantifier
compileQuantScoped :: QuantifiableScoped a => Quantifier -> String -> (SBV a -> Symbolic SBool) -> Symbolic SBool
compileQuantScoped ForallQ = universalScoped
compileQuantScoped _ = existentialScoped

-- | Represents symbolic values which can be quantified over inside the solver
-- | Mostly this just overrides to SBV's in-built quantification, but sometimes
-- | we want some custom things to happen when we quantify
class QuantifiableScoped a where
  universalScoped :: String -> (SBV a -> Symbolic SBool) -> Symbolic SBool
  existentialScoped :: String -> (SBV a -> Symbolic SBool) -> Symbolic SBool

instance QuantifiableScoped Integer where
  universalScoped v = forAll [v]
  existentialScoped v = forSome [v]

instance QuantifiableScoped Float where
  universalScoped v = forAll [v]
  existentialScoped v = forSome [v]


-- Compile a constraint into a symbolic bool (SBV predicate)
compile :: (?globals :: Globals) =>
  Ctxt SGrade -> Constraint -> Symbolic SBool

compile vars (Eq _ c1 c2 t) =
  bindM2And' eqConstraint (compileCoeffect (normalise c1) t vars) (compileCoeffect (normalise c2) t vars)

compile vars (Neq _ c1 c2 t) =
  bindM2And' (\c1' c2' -> fmap sNot (eqConstraint c1' c2')) (compileCoeffect (normalise c1) t vars) (compileCoeffect (normalise c2) t vars)

-- Assumes that c3 is already existentially bound
compile vars (Lub _ c1 c2 c3@(CVar v) t) =

  case t of
    {-
    -- An alternate procedure for computing least-upper bounds
    -- I was experimenting with this to see if it could speed up solving.
    -- For largely symbolic constraints, it doesn't seem to make much difference.

    -- Use the join when `extendedNat` is involved
    (isInterval -> Just t') | t' == extendedNat -> do
      (s1, p1) <- compileCoeffect c1 t vars
      (s2, p2) <- compileCoeffect c2 t vars
      (s3, p3) <- compileCoeffect c3 t vars
      lub   <- s1 `symGradeJoin` s2
      eq    <- s3 `symGradeEq` lub
      return (p1 .&& p2 .&& p3 .&& eq) -}

    _ -> do
      (s1, p1) <- compileCoeffect (normalise c1) t vars
      (s2, p2) <- compileCoeffect (normalise c2) t vars
      (s3, p3) <- compileCoeffect (normalise c3) t vars
      -- s3 is an upper bound
      pa1 <- approximatedByOrEqualConstraint s1 s3
      pb1 <- approximatedByOrEqualConstraint s2 s3
      --- and it is the least such upper bound
      pc <- freshCVarScoped compileQuantScoped (internalName v <> ".up") t ForallQ
              (\(py, y) -> do
                pc1 <- approximatedByOrEqualConstraint s1 y
                pc2 <- approximatedByOrEqualConstraint s2 y
                pc3 <- approximatedByOrEqualConstraint s3 y
                return ((py .&& pc1 .&& pc2) .=> pc3))
      return (p1 .&& p2 .&& p3 .&& pa1 .&& pb1 .&& pc)

compile vars (ApproximatedBy _ c1 c2 t) =
  bindM2And' approximatedByOrEqualConstraint (compileCoeffect c1 t vars) (compileCoeffect c2 t vars)

compile vars (Lt s c1 c2) =
  bindM2And' symGradeLess (compileCoeffect c1 (TyCon $ mkId "Nat") vars) (compileCoeffect c2 (TyCon $ mkId "Nat") vars)

compile vars (Gt s c1 c2) =
  bindM2And' symGradeGreater (compileCoeffect c1 (TyCon $ mkId "Nat") vars) (compileCoeffect c2 (TyCon $ mkId "Nat") vars)

compile vars (LtEq s c1 c2) =
  bindM2And' symGradeLessEq (compileCoeffect c1 (TyCon $ mkId "Nat") vars) (compileCoeffect c2 (TyCon $ mkId "Nat") vars)

compile vars (GtEq s c1 c2) =
  bindM2And' symGradeGreaterEq (compileCoeffect c1 (TyCon $ mkId "Nat") vars) (compileCoeffect c2 (TyCon $ mkId "Nat") vars)

-- TODO: I think this is deprecated (DAO 12/08/2019)
-- NonZeroPromotableTo s c means that:
compile vars (NonZeroPromotableTo s x c t) = do
  -- exists x .
  freshCVarScoped compileQuantScoped (internalName x) t InstanceQ
   (\(req, xVar) -> do

    -- x != 0
    nonZero <- compile ((x, xVar) : vars) (Neq s (CZero t) (CVar x) t)

    -- x * 1 == c
    promotableToC <- compile ((x, xVar) : vars) (Eq s (CTimes (COne t) (CVar x)) c t)

    return (req .&& nonZero .&& promotableToC))

compile vars c = error $ "Internal bug: cannot compile " <> show c

-- | Compile a coeffect term into its symbolic representation
-- | (along with any additional predicates)
compileCoeffect :: (?globals :: Globals) =>
  Coeffect -> Type -> [(Id, SGrade)] -> Symbolic (SGrade, SBool)

compileCoeffect (CSig c k) _ ctxt = compileCoeffect c k ctxt

compileCoeffect (Level n) (TyCon k) _ | internalName k == "Level" =
  return (SLevel . fromInteger . toInteger $ n, sTrue)

-- TODO: I think the following two cases are deprecatd: (DAO 12/08/2019)
compileCoeffect (Level n) (isProduct -> Just (TyCon k, t2)) vars | internalName k == "Level" = do
  (g, p) <- compileCoeffect (COne t2) t2 vars
  return (SProduct (SLevel . fromInteger . toInteger $ n) g, p)

compileCoeffect (Level n) (isProduct -> Just (t1, TyCon k)) vars | internalName k == "Level" = do
  (g, p) <- compileCoeffect (COne t1) t1 vars
  return (SProduct g (SLevel . fromInteger . toInteger $ n), p)

-- Any polymorphic `Inf` gets compiled to the `Inf : [0..inf]` coeffect
-- TODO: see if we can erase this, does it actually happen anymore?
compileCoeffect (CInfinity (Just (TyVar _))) _ _ = return (zeroToInfinity, sTrue)
compileCoeffect (CInfinity Nothing) _ _ = return (zeroToInfinity, sTrue)
compileCoeffect (CInfinity _) t _| t == extendedNat =
  return (SExtNat SNatX.inf, sTrue)

compileCoeffect (CNat n) k _ | k == nat =
  return (SNat  . fromInteger . toInteger $ n, sTrue)

compileCoeffect (CNat n) k _ | k == extendedNat =
  return (SExtNat . fromInteger . toInteger $ n, sTrue)

compileCoeffect (CFloat r) (TyCon k) _ | internalName k == "Q" =
  return (SFloat  . fromRational $ r, sTrue)

compileCoeffect (CSet xs) (TyCon k) _ | internalName k == "Set" =
  return (SSet . S.fromList $ map (first mkId) xs, sTrue)

compileCoeffect (CVar v) _ vars =
   case lookup v vars of
    Just cvar -> return (cvar, sTrue)
    _ -> solverError $ "Looking up a variable '" <> show v <> "' in " <> show vars

compileCoeffect c@(CMeet n m) k vars =
  bindM2And symGradeMeet (compileCoeffect n k vars) (compileCoeffect m k vars)

compileCoeffect c@(CJoin n m) k vars =
  bindM2And symGradeJoin (compileCoeffect n k vars) (compileCoeffect m k vars)

compileCoeffect c@(CPlus n m) k vars =
  bindM2And symGradePlus (compileCoeffect n k vars) (compileCoeffect m k vars)

compileCoeffect c@(CTimes n m) k vars =
  bindM2And symGradeTimes (compileCoeffect n k vars) (compileCoeffect m k vars)

compileCoeffect c@(CMinus n m) k vars =
  bindM2And symGradeMinus (compileCoeffect n k vars) (compileCoeffect m k vars)

compileCoeffect c@(CExpon n m) k vars = do
  (g1, p1) <- compileCoeffect n k vars
  (g2, p2) <- compileCoeffect m k vars
  case (g1, g2) of
    (SNat n1, SNat n2) -> return (SNat (n1 .^ n2), p1 .&& p2)
    _ -> solverError $ "Failed to compile: " <> pretty c <> " of kind " <> pretty k

compileCoeffect c@(CInterval lb ub) (isInterval -> Just t) vars = do
  (lower, p1) <- compileCoeffect lb t vars
  (upper, p2) <- compileCoeffect ub t vars
  intervalConstraint <- symGradeLessEq lower upper
  return $ (SInterval lower upper, p1 .&& p2 .&& intervalConstraint)

compileCoeffect (CZero k') k vars  =
  case (k', k) of
    (TyCon k', TyCon k) -> assert (internalName k' == internalName k) $
      case internalName k' of
        "Level"     -> return (SLevel (literal unusedRepresentation), sTrue)
        "Nat"       -> return (SNat 0, sTrue)
        "Q"         -> return (SFloat (fromRational 0), sTrue)
        "Set"       -> return (SSet (S.fromList []), sTrue)
        "OOZ"       -> return (SOOZ sFalse, sTrue)
        _           -> solverError $ "I don't know how to compile a 0 for " <> pretty k'
    (otherK', otherK) | (otherK' == extendedNat || otherK == extendedNat) ->
      return (SExtNat 0, sTrue)

    (isProduct -> Just (t1, t2), isProduct -> Just (t1', t2')) ->
      liftM2And SProduct
        (compileCoeffect (CZero t1) t1' vars)
        (compileCoeffect (CZero t2) t2' vars)

    (isInterval -> Just t, isInterval -> Just t') ->
      liftM2And SInterval
        (compileCoeffect (CZero t) t' vars)
        (compileCoeffect (CZero t) t' vars)

    (TyVar _, _) -> return (SUnknown (SynLeaf (Just 0)), sTrue)
    _ -> solverError $ "I don't know how to compile a 0 for " <> pretty k'

compileCoeffect (COne k') k vars =
  case (k', k) of
    (TyCon k', TyCon k) -> assert (internalName k' == internalName k) $
      case internalName k' of
        "Level"     -> return (SLevel (literal privateRepresentation), sTrue)
        "Nat"       -> return (SNat 1, sTrue)
        "Q"         -> return (SFloat (fromRational 1), sTrue)
        "Set"       -> return (SSet (S.fromList []), sTrue)
        "OOZ"       -> return (SOOZ sTrue, sTrue)
        _           -> solverError $ "I don't know how to compile a 1 for " <> pretty k'

    (otherK', otherK) | (otherK' == extendedNat || otherK == extendedNat) ->
      return (SExtNat 1, sTrue)

    (isProduct -> Just (t1, t2), isProduct -> Just (t1', t2')) ->
      liftM2And SProduct
        (compileCoeffect (COne t1) t1' vars)
        (compileCoeffect (COne t2) t2' vars)

    -- Build an interval for 1
    (isInterval -> Just t, isInterval -> Just t') -> do
      liftM2And SInterval
          (compileCoeffect (COne t) t' vars)
          (compileCoeffect (COne t) t' vars)

    (TyVar _, _) -> return (SUnknown (SynLeaf (Just 1)), sTrue)

    _ -> solverError $ "I don't know how to compile a 1 for " <> pretty k'

compileCoeffect (CProduct c1 c2) (isProduct -> Just (t1, t2)) vars =
  liftM2And SProduct (compileCoeffect c1 t1 vars) (compileCoeffect c2 t2 vars)

-- For grade-polymorphic coeffects, that have come from a nat
-- expression (sometimes this is just from a compounded expression of 1s),
-- perform the injection from Natural numbers to arbitrary semirings
compileCoeffect (CNat n) (TyVar _) _ | n > 0 =
  return (SUnknown (injection n), sTrue)
    where
      injection 0 = SynLeaf (Just 0)
      injection 1 = SynLeaf (Just 1)
      injection n = SynPlus (SynLeaf (Just 1)) (injection (n-1))

-- Trying to compile a coeffect from a promotion that was never
-- constrained further
compileCoeffect c (TyVar v) _ =
  return (SUnknown (SynLeaf Nothing), sTrue)

compileCoeffect coeff ckind _ =
   solverError $ "Can't compile a coeffect: " <> pretty coeff <> " {" <> (show coeff) <> "}"
        <> " of kind " <> pretty ckind

-- | Generate equality constraints for two symbolic coeffects
eqConstraint :: SGrade -> SGrade -> Symbolic SBool
eqConstraint (SNat n) (SNat m)     = return $ n .== m
eqConstraint (SFloat n) (SFloat m) = return $ n .== m
eqConstraint (SLevel l) (SLevel k) = return $ l .== k
eqConstraint u@(SUnknown{}) u'@(SUnknown{}) = symGradeEq u u'
eqConstraint (SExtNat x) (SExtNat y) = return $ x .== y
eqConstraint SPoint SPoint           = return sTrue

eqConstraint (SInterval lb1 ub1) (SInterval lb2 ub2) =
  liftM2 (.&&) (eqConstraint lb1 lb2) (eqConstraint ub1 ub2)

eqConstraint s t | isSProduct s && isSProduct t =
  either solverError id (applyToProducts symGradeEq (.&&) (const sTrue) s t)

eqConstraint x y =
  solverError $ "Kind error trying to generate equality " <> show x <> " = " <> show y

-- | Generate less-than-equal constraints for two symbolic coeffects
approximatedByOrEqualConstraint :: SGrade -> SGrade -> Symbolic SBool
approximatedByOrEqualConstraint (SNat n) (SNat m)      = return $ n .== m
approximatedByOrEqualConstraint (SFloat n) (SFloat m)  = return $ n .<= m
approximatedByOrEqualConstraint SPoint SPoint          = return $ sTrue
approximatedByOrEqualConstraint (SExtNat x) (SExtNat y) = return $ x .== y
approximatedByOrEqualConstraint (SOOZ s) (SOOZ r) = pure $ s .== r
approximatedByOrEqualConstraint (SSet s) (SSet t) =
  return $ if s == t then sTrue else sFalse

approximatedByOrEqualConstraint (SLevel l) (SLevel k) =
    -- Private <= Public
  return
    $ ite (l .== literal unusedRepresentation) sTrue
      $ ite (l .== literal privateRepresentation) sTrue
        $ ite (k .== literal publicRepresentation) sTrue sFalse

approximatedByOrEqualConstraint s t | isSProduct s && isSProduct t =
  either solverError id (applyToProducts approximatedByOrEqualConstraint (.&&) (const sTrue) s t)

-- Perform approximation when nat-like grades are involved
-- e.g. [2..3] <= [0..10]  iff (0 <= 2 and 3 <= 10)
approximatedByOrEqualConstraint (SInterval lb1 ub1) (SInterval lb2 ub2)
    | natLike lb1 || natLike lb2 || natLike ub1 || natLike ub2 =
  liftM2 (.&&) (symGradeLessEq lb2 lb1) (symGradeLessEq ub1 ub2)

-- if intervals are not nat-like then use the notion of approximation
-- given here
approximatedByOrEqualConstraint (SInterval lb1 ub1) (SInterval lb2 ub2) =
  liftM2 (.&&) (approximatedByOrEqualConstraint lb2 lb1)
                (approximatedByOrEqualConstraint ub1 ub2)

approximatedByOrEqualConstraint u@(SUnknown{}) u'@(SUnknown{}) =
  lazyOrSymbolicM (symGradeEq u u') (symGradeLess u u')

approximatedByOrEqualConstraint x y =
  solverError $ "Kind error trying to generate " <> show x <> " <= " <> show y


trivialUnsatisfiableConstraints :: Pred -> [Constraint]
trivialUnsatisfiableConstraints
    = concatMap unsat
    . map normaliseConstraint
    . positiveConstraints
  where
    -- Only check trivial constraints in positive positions
    -- This means we don't report a branch concluding false trivially
    -- TODO: may check trivial constraints everywhere?

    -- TODO: this just ignores disjunction constraints
    -- TODO: need to check that all are unsat- but this request a different
    --       representation here.
    positiveConstraints =
        predFold concat (\_ -> []) (\_ q -> q) (\x -> [x]) id (\_ _ p -> p) (\_ _ p -> p)

    -- All the (trivially) unsatisfiable constraints
    unsat :: Constraint -> [Constraint]
    unsat c@(Eq _ c1 c2 _)  = if (c1 `neqC` c2) then [c] else []
    unsat c@(Neq _ c1 c2 _) = if (c1 `neqC` c2) then [] else [c]
    unsat c@(ApproximatedBy{}) = approximatedByC c
    unsat c@(NonZeroPromotableTo _ _ (CZero _) _) = [c]
    unsat (NonZeroPromotableTo _ _ _ _) = []
    -- TODO: look at this information
    unsat Lub{} = []
    unsat (Lt _ c1 c2) = []
    unsat (Gt _ c1 c2) = []
    unsat (LtEq _ c1 c2) = []
    unsat (GtEq _ c1 c2) = []

    -- TODO: unify this with eqConstraint and approximatedByOrEqualConstraint
    -- Attempt to see if one coeffect is trivially greater than the other
    approximatedByC :: Constraint -> [Constraint]
    approximatedByC c@(ApproximatedBy _ (CNat n) (CNat m) _) | n /= m = [c]
    approximatedByC c@(ApproximatedBy _ (Level n) (Level m) _) | n > m = [c]
    approximatedByC c@(ApproximatedBy _ (CFloat n) (CFloat m) _) | n > m = [c]
    -- Nat like intervals
    approximatedByC c@(ApproximatedBy _
                        (CInterval (CNat lb1) (CNat ub1))
                        (CInterval (CNat lb2) (CNat ub2)) _)
        | not $ (lb2 <= lb1) && (ub1 <= ub2) = [c]

    approximatedByC (ApproximatedBy s (CProduct c1 c2) (CProduct d1 d2) (isProduct -> Just (t1, t2))) =
      (approximatedByC (ApproximatedBy s c1 d1 t1)) ++ (approximatedByC (ApproximatedBy s c2 d2 t2))

    approximatedByC (ApproximatedBy s c (CProduct d1 d2) (isProduct -> Just (t1, t2))) =
      (approximatedByC (ApproximatedBy s c d1 t1)) ++ (approximatedByC (ApproximatedBy s c d2 t2))

    approximatedByC (ApproximatedBy s (CProduct c1 c2) d (isProduct -> Just (t1, t2))) =
      (approximatedByC (ApproximatedBy s c1 d t1)) ++ (approximatedByC (ApproximatedBy s c2 d t2))

    approximatedByC _ = []

    -- Attempt to see if one coeffect is trivially not equal to the other
    neqC :: Coeffect -> Coeffect -> Bool
    neqC (CNat n) (CNat m) = n /= m
    neqC (Level n) (Level m)   = n /= m
    neqC (CFloat n) (CFloat m) = n /= m
    --neqC (CInterval lb1 ub1) (CInterval lb2 ub2) =
    --   neqC lb1 lb2 || neqC ub1 ub2
    neqC _ _                   = False

data SolverResult
  = QED
  | NotValid String
  | NotValidTrivial [Constraint]
  | Timeout
  | SolverProofError String
  | OtherSolverError String

provePredicate
  :: (?globals :: Globals)
  => Pred                    -- Predicate
  -> IO SolverResult
provePredicate predicate
  | isTrivial predicate = do
      debugM "solveConstraints" "Skipping solver because predicate is trivial."
      return QED
  | otherwise = do
      let (sbvTheorem, _, unsats) = compileToSBV predicate
      ThmResult thmRes <- proveWith defaultSMTCfg $ do --  -- proveWith cvc4 {verbose=True}
        case solverTimeoutMillis of
          n | n <= 0 -> return ()
          n -> setTimeOut n
        sbvTheorem

      return $ case thmRes of
        -- we're good: the negation of the theorem is unsatisfiable
        Unsatisfiable {} -> QED
        ProofError _ msgs _ -> SolverProofError $ unlines msgs
        Unknown _ UnknownTimeOut -> Timeout
        Unknown _ reason  -> OtherSolverError $ show reason
        _ ->
          case getModelAssignment thmRes of
            -- Main 'Falsifiable' result
            Right (False, assg :: [ Integer ] ) ->
              -- Show any trivial inequalities
              if not (null unsats)
                then NotValidTrivial unsats
                else
                  -- Show fatal error, with prover result
                  {-
                  negated <- liftIO . sat $ sbvSatTheorem
                  print $ show $ getModelDictionary negated
                  case (getModelAssignment negated) of
                    Right (_, assg :: [Integer]) -> do
                      print $ show assg
                    Left msg -> print $ show msg
                  -}
                   NotValid $ "is " <> show (ThmResult thmRes)
            Right (True, _) -> NotValid "returned probable model."
            Left str -> OtherSolverError str

-- Useful combinators here
-- Generalises `bindM2` to functions which return also a symbolic grades
-- which should be combined via .&&
bindM2And :: Monad m => (t1 -> t2 -> m b) -> m (t1, SBool) -> m (t2, SBool) -> m (b, SBool)
bindM2And k ma mb = do
  (a, p) <- ma
  (b, q) <- mb
  c <- k a b
  return (c, p .&& q)

bindM2And' :: Monad m => (t1 -> t2 -> m SBool) -> m (t1, SBool) -> m (t2, SBool) -> m SBool
bindM2And' k ma mb = do
  (a, p) <- ma
  (b, q) <- mb
  c <- k a b
  return (p .&& q .&& c)

liftM2And :: Monad m => (t1 -> t2 -> b) -> m (t1, SBool) -> m (t2, SBool) -> m (b, SBool)
liftM2And k = bindM2And (\a b -> return (k a b))