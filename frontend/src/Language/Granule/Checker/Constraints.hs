{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}


-- | Deals with compilation of coeffects into symbolic representations of SBV
module Language.Granule.Checker.Constraints where

--import Data.Foldable (foldrM)
import Data.SBV hiding (kindOf, name, symbolic)
import qualified Data.SBV.Set as S
import Data.Maybe (mapMaybe)
import Control.Monad (liftM2)
import Control.Monad.IO.Class

import Language.Granule.Checker.Predicates
import Language.Granule.Context (Ctxt)

import Language.Granule.Checker.Constraints.SymbolicGrades
import qualified Language.Granule.Checker.Constraints.SNatX as SNatX

import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type
import Language.Granule.Utils

import qualified System.Clock as Clock

-- | Compile constraint into an SBV symbolic bool, along with a list of
-- | constraints which are trivially unequal (if such things exist) (e.g., things like 1=0).
compileToSBV :: (?globals :: Globals)
  => Pred -> Ctxt (Type, Quantifier)
  -> (Symbolic SBool, Symbolic SBool, [Constraint])
compileToSBV predicate tyVarContext =
  (buildTheoremNew (reverse tyVarContext) []
  , undefined -- buildTheorem sNot (compileQuant . flipQuant)
  , trivialUnsatisfiableConstraints predicate')

  where
    -- flipQuant ForallQ   = InstanceQ
    -- flipQuant InstanceQ = ForallQ
    -- flipQuant BoundQ    = BoundQ

    predicate' = rewriteBindersInPredicate tyVarContext predicate

    buildTheoremNew :: Ctxt (Type, Quantifier) -> Ctxt SGrade -> Symbolic SBool
    buildTheoremNew [] solverVars =
      buildTheorem' solverVars predicate

    buildTheoremNew ((v, (t, q)) : ctxt) solverVars =
      freshSolverVarScoped compileQuantScoped (internalName v) t q
         (\(varPred, solverVar) -> do
             pred <- buildTheoremNew ctxt ((v, solverVar) : solverVars)
             case q of
              ForallQ -> return $ varPred .=> pred
              _       -> return $ varPred .&& pred)

    -- Build the theorem, doing local creation of universal variables
    -- when needed (see Impl case)
    buildTheorem' :: Ctxt SGrade -> Pred -> Symbolic SBool
    buildTheorem' solverVars (Conj ps) = do
      ps' <- mapM (buildTheorem' solverVars) ps
      return $ sAnd ps'

    buildTheorem' solverVars (Disj ps) = do
      ps' <- mapM (buildTheorem' solverVars) ps
      return $ sOr ps'

    buildTheorem' solverVars (Impl [] p1 p2) = do
        p1' <- buildTheorem' solverVars p1
        p2' <- buildTheorem' solverVars p2
        return $ p1' .=> p2'

    buildTheorem' solverVars (NegPred p) = do
        p' <- buildTheorem' solverVars p
        return $ sNot p'

    buildTheorem' solverVars (Exists v k p) =
      if v `elem` (freeVars p)
        -- optimisation
        then
          freshSolverVarScoped compileQuantScoped (internalName v) k InstanceQ
            (\(varPred, solverVar) -> do
              pred' <- buildTheorem' ((v, solverVar) : solverVars) p
              return (varPred .&& pred'))

        else
          buildTheorem' solverVars p

    buildTheorem' solverVars (Impl ((v, k):vs) p p') =
      if v `elem` (freeVars p <> freeVars p')
        -- If the quantified variable appears in the theorem
        then
          freshSolverVarScoped compileQuantScoped (internalName v) k ForallQ
                (\(varPred, solverVar) -> do
                  pred' <- buildTheorem' ((v, solverVar) : solverVars) (Impl vs p p')
                  return (varPred .=> pred'))
        else
          -- An optimisation, don't bother quantifying things
          -- which don't appear in the theorem anyway

          buildTheorem' solverVars (Impl vs p p')

    buildTheorem' solverVars (Con cons) =
      compile solverVars cons

-- | Symbolic coeffect representing 0..Inf
zeroToInfinity :: SGrade
zeroToInfinity = SInterval (SExtNat $ SNatX.SNatX 0) (SExtNat SNatX.inf)

freshSolverVarScoped ::
    (forall a . QuantifiableScoped a => Quantifier -> String -> (SBV a -> Symbolic SBool) -> Symbolic SBool)
  -> String
  -> Type
  -> Quantifier
  -> ((SBool, SGrade) -> Symbolic SBool)
  -> Symbolic SBool
freshSolverVarScoped quant name (isInterval -> Just t) q k =

  freshSolverVarScoped quant (name <> ".lower") t q
   (\(predLb, solverVarLb) ->
      freshSolverVarScoped quant (name <> ".upper") t q
       (\(predUb, solverVarUb) -> do
          -- Respect the meaning of intervals
          lessEq <- symGradeLessEq solverVarLb solverVarUb
          k ( predLb .&& predUb .&& lessEq
            , SInterval solverVarLb solverVarUb )
          ))

freshSolverVarScoped quant name (isProduct -> Just (t1, t2)) q k =

  freshSolverVarScoped quant (name <> ".fst") t1 q
    (\(predFst, solverVarFst) ->
      freshSolverVarScoped quant (name <> ".snd") t2 q
        (\(predSnd, solverVarSnd) ->
          k (predFst .&& predSnd, SProduct solverVarFst solverVarSnd)))

freshSolverVarScoped quant name (TyCon (internalName -> "Q")) q k =
  -- Floats (rationals)
    quant q name (\solverVar -> k (sTrue, SFloat solverVar))

freshSolverVarScoped quant name (TyCon (internalName -> "Sec")) q k =
    quant q name (\solverVar -> k (sTrue, SSec solverVar))

freshSolverVarScoped quant name (TyCon (internalName -> "LNL")) q k =
    quant q name (\solverVar -> k (sTrue, SLNL solverVar))

freshSolverVarScoped quant name (TyCon conName) q k =
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

freshSolverVarScoped quant name t q k | t == extendedNat = do
   quant q name (\solverVar ->
    k (SNatX.representationConstraint solverVar
     , SExtNat (SNatX.SNatX solverVar)))

freshSolverVarScoped quant name (TyVar v) q k =
  quant q name (\solverVar -> k (sTrue, SUnknown $ SynLeaf $ Just solverVar))

freshSolverVarScoped quant name (Language.Granule.Syntax.Type.isSet -> elemTy) q k =
  quant q name (\solverVar -> k (sTrue, SSet solverVar))

-- freshSolverVarScoped _ _ t _ _ =
--   solverError $ "Trying to make a fresh solver variable for a grade of type: "
--       <> show t <> " but I don't know how."

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

instance QuantifiableScoped Bool where
  universalScoped v = forAll [v]
  existentialScoped v = forSome [v]

instance QuantifiableScoped Float where
  universalScoped v = forAll [v]
  existentialScoped v = forSome [v]

instance QuantifiableScoped (RCSet SSetElem) where
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
compile vars (Lub _ c1 c2 c3@(TyVar v) t) =
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
      pc <- freshSolverVarScoped compileQuantScoped (internalName v <> ".up") t ForallQ
              (\(py, y) -> do
                pc1 <- approximatedByOrEqualConstraint s1 y
                pc2 <- approximatedByOrEqualConstraint s2 y
                pc3 <- approximatedByOrEqualConstraint s3 y
                return ((py .&& pc1 .&& pc2) .=> pc3))
      return (p1 .&& p2 .&& p3 .&& pa1 .&& pb1 .&& pc)

compile vars (ApproximatedBy _ c1 c2 t) =
  bindM2And' approximatedByOrEqualConstraint (compileCoeffect (normalise c1) t vars) (compileCoeffect (normalise c2) t vars)

compile vars (Lt s c1 c2) =
  bindM2And' symGradeLess (compileCoeffect c1 (TyCon $ mkId "Nat") vars) (compileCoeffect c2 (TyCon $ mkId "Nat") vars)

compile vars (Gt s c1 c2) =
  bindM2And' symGradeGreater (compileCoeffect c1 (TyCon $ mkId "Nat") vars) (compileCoeffect c2 (TyCon $ mkId "Nat") vars)

compile vars (LtEq s c1 c2) =
  bindM2And' symGradeLessEq (compileCoeffect c1 (TyCon $ mkId "Nat") vars) (compileCoeffect c2 (TyCon $ mkId "Nat") vars)

compile vars (GtEq s c1 c2) =
  bindM2And' symGradeGreaterEq (compileCoeffect c1 (TyCon $ mkId "Nat") vars) (compileCoeffect c2 (TyCon $ mkId "Nat") vars)

compile vars c = error $ "Internal bug: cannot compile " <> show c

-- | Compile a coeffect term into its symbolic representation
-- | (along with any additional predicates)
-- |
-- | `compileCoeffect r t context` compiles grade `r` of type `t`.
compileCoeffect :: (?globals :: Globals) =>
  Coeffect -> Type -> [(Id, SGrade)] -> Symbolic (SGrade, SBool)

compileCoeffect (TySig c k) _ ctxt = compileCoeffect c k ctxt

compileCoeffect (TyCon name) (TyCon (internalName -> "Level")) _ = do
  let n = case internalName name of
            "Unused"  -> unusedRepresentation
            "Private" -> privateRepresentation
            "Public"  -> publicRepresentation
            c         -> error $ "Cannot compile " <> show c

  return (SLevel . fromInteger . toInteger $ n, sTrue)

compileCoeffect (TyCon name) (TyCon (internalName -> "LNL")) _ = do
  case internalName name of
    "Lin"    -> return (SLNL sFalse, sTrue)
    "NonLin" -> return (SLNL sTrue, sTrue)
    c -> error $ "Cannot compile " <> show c <> " as a LNL semiring"

compileCoeffect (TyCon name) (TyCon (internalName -> "Sec")) _ = do
  case internalName name of
    "Hi" -> return (SSec hiRepresentation, sTrue)
    "Lo" -> return (SSec loRepresentation, sTrue)
    c    -> error $ "Cannot compile " <> show c <> " as a Sec semiring"

-- TODO: I think the following two cases are deprecatd: (DAO 12/08/2019)
compileCoeffect (TyApp (TyCon (internalName -> "Level")) (TyInt n)) (isProduct -> Just (TyCon (internalName -> "Level"), t2)) vars = do
  (g, p) <- compileCoeffect (TyInt 1) t2 vars
  return (SProduct (SLevel . fromInteger . toInteger $ n) g, p)

compileCoeffect (TyApp (TyCon (internalName -> "Level")) (TyInt n)) (isProduct -> Just (t1, TyCon (internalName -> "Level"))) vars = do
  (g, p) <- compileCoeffect (TyInt 1) t1 vars
  return (SProduct g (SLevel . fromInteger . toInteger $ n), p)

compileCoeffect (TyCon (internalName -> "Infinity")) t _ | t == extendedNat =
  return (SExtNat SNatX.inf, sTrue)
-- Any polymorphic `Inf` gets compiled to the `Inf : [0..inf]` coeffect
-- TODO: see if we can erase this, does it actually happen anymore?
compileCoeffect (TyCon (internalName -> "Infinity")) _ _ = return (zeroToInfinity, sTrue)

-- Effect 0 : Nat
compileCoeffect (TyCon (internalName -> "Pure")) (TyCon (internalName -> "Nat")) _ =
  return (SNat 0, sTrue)

compileCoeffect (TyInt n) k _ | k == nat =
  return (SNat  . fromInteger . toInteger $ n, sTrue)

compileCoeffect (TyInt n) k _ | k == extendedNat =
  return (SExtNat . fromInteger . toInteger $ n, sTrue)

compileCoeffect (TyGrade k' n) k _ | k == nat && (k' == Nothing || k' == Just nat) =
  return (SNat  . fromInteger . toInteger $ n, sTrue)

compileCoeffect (TyGrade k' n) k _ | k == extendedNat && (k' == Nothing || k' == Just extendedNat)=
  return (SExtNat . fromInteger . toInteger $ n, sTrue)

compileCoeffect (TyRational r) (TyCon k) _ | internalName k == "Q" =
  return (SFloat  . fromRational $ r, sTrue)

compileCoeffect (TySet xs) (TyCon k) _ | internalName k == "Set" =
    return (SSet . S.fromList $ mapMaybe justTyConNames xs, sTrue)
  where
    justTyConNames (TyCon x) = Just (internalName x)
    justTyConNames t = error $ "Cannot have a type " ++ show t ++ " in a symbolic list"

compileCoeffect (TyVar v) _ vars =
   case lookup v vars of
    Just cvar -> return (cvar, sTrue)
    _ -> solverError $ "Looking up a variable '" <> show v <> "' in " <> show vars

compileCoeffect c@(TyInfix TyOpMeet n m) k vars =
  bindM2And symGradeMeet (compileCoeffect n k vars) (compileCoeffect m k vars)

compileCoeffect c@(TyInfix TyOpJoin n m) k vars =
  bindM2And symGradeJoin (compileCoeffect n k vars) (compileCoeffect m k vars)

compileCoeffect c@(TyInfix TyOpPlus n m) k vars =
  bindM2And symGradePlus (compileCoeffect n k vars) (compileCoeffect m k vars)

compileCoeffect c@(TyInfix TyOpTimes n m) k vars =
  bindM2And symGradeTimes (compileCoeffect n k vars) (compileCoeffect m k vars)

compileCoeffect c@(TyInfix TyOpMinus n m) k vars =
  bindM2And symGradeMinus (compileCoeffect n k vars) (compileCoeffect m k vars)

compileCoeffect c@(TyInfix TyOpExpon n m) k vars = do
  (g1, p1) <- compileCoeffect n k vars
  (g2, p2) <- compileCoeffect m k vars
  case (g1, g2) of
    (SNat n1, SNat n2) -> return (SNat (n1 .^ n2), p1 .&& p2)
    _ -> solverError $ "Failed to compile: " <> pretty c <> " of kind " <> pretty k

compileCoeffect c@(TyInfix TyOpInterval lb ub) (isInterval -> Just t) vars = do
  (lower, p1) <- compileCoeffect lb t vars
  (upper, p2) <- compileCoeffect ub t vars
  intervalConstraint <- symGradeLessEq lower upper
  return $ (SInterval lower upper, p1 .&& p2 .&& intervalConstraint)

compileCoeffect (TyCon name) (isInterval -> Just t) vars | t == extendedNat = do
  case internalName name of
    "Lin"    -> return (SInterval (SExtNat 1) (SExtNat 1), sTrue)
    "NonLin" -> return (SInterval (SExtNat 0) (SExtNat SNatX.inf), sTrue)
    c -> error $ "Cannot compile " <> show c <> " as a Interval (Extended Nat) semiring"

compileCoeffect (TyGrade k' 0) k vars = do
  k <- matchTypes k k'
  case k of
    (TyCon k') ->
      case internalName k' of
        "Level"     -> return (SLevel (literal unusedRepresentation), sTrue)
        "Sec"       -> return (SSec hiRepresentation, sTrue)
        "Nat"       -> return (SNat 0, sTrue)
        "Q"         -> return (SFloat (fromRational 0), sTrue)
        "Set"       -> return (SSet (S.fromList []), sTrue)
        "OOZ"       -> return (SOOZ sFalse, sTrue)
        "LNL"       -> return (SLNL sTrue, sTrue)
        _           -> solverError $ "I don't know how to compile a 0 for " <> pretty k
    otherK | otherK == extendedNat ->
      return (SExtNat 0, sTrue)

    (isProduct -> Just (t1, t2)) ->
      liftM2And SProduct
        (compileCoeffect (TyGrade (Just t1) 0) t1 vars)
        (compileCoeffect (TyGrade (Just t2) 0) t2 vars)

    (isInterval -> Just t) ->
      liftM2And SInterval
        (compileCoeffect (TyGrade (Just t) 0) t vars)
        (compileCoeffect (TyGrade (Just t) 0) t vars)

    (TyVar _) -> return (SUnknown (SynLeaf (Just 0)), sTrue)

    _ -> solverError $ "I don't know how to compile a 0 for " <> pretty k

compileCoeffect (TyGrade k' 1) k vars = do
  k <- matchTypes k k'
  case k of
    TyCon k ->
      case internalName k of
        "Level"     -> return (SLevel (literal privateRepresentation), sTrue)
        "Sec"       -> return (SSec loRepresentation, sTrue)
        "Nat"       -> return (SNat 1, sTrue)
        "Q"         -> return (SFloat (fromRational 1), sTrue)
        "Set"       -> return (SSet (S.fromList []), sTrue)
        "OOZ"       -> return (SOOZ sTrue, sTrue)
        "LNL"       -> return (SLNL sFalse, sTrue)
        _           -> solverError $ "I don't know how to compile a 1 for " <> pretty k

    otherK | otherK == extendedNat ->
      return (SExtNat 1, sTrue)

    (isProduct -> Just (t1, t2)) ->
      liftM2And SProduct
        (compileCoeffect (TyGrade (Just t1) 1) t1 vars)
        (compileCoeffect (TyGrade (Just t2) 1) t2 vars)

    (isInterval -> Just t) ->
      liftM2And SInterval
        (compileCoeffect (TyGrade (Just t) 1) t vars)
        (compileCoeffect (TyGrade (Just t) 1) t vars)

    (TyVar _) -> return (SUnknown (SynLeaf (Just 1)), sTrue)

    _ -> solverError $ "I don't know how to compile a 1 for " <> pretty k

compileCoeffect (isProduct -> Just (c1, c2)) (isProduct -> Just (t1, t2)) vars =
  liftM2And SProduct (compileCoeffect c1 t1 vars) (compileCoeffect c2 t2 vars)

-- Perform the injection from natural numbers to arbitrary semirings
compileCoeffect (TyGrade k' n) k vars | n > 0 = do
  -- Check that we have agreement here
  _ <- matchTypes k k'
  compileCoeffect (injection n) k vars
    where
      injection 0 = TyGrade (Just k) 0
      injection 1 = TyGrade (Just k) 1
      injection n = TyInfix TyOpPlus (TyGrade (Just k) 1) (injection (n-1))

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
  symGradeEq x y

-- | Generate less-than-equal constraints for two symbolic coeffects
approximatedByOrEqualConstraint :: SGrade -> SGrade -> Symbolic SBool
approximatedByOrEqualConstraint (SNat n) (SNat m)      = return $ n .== m
approximatedByOrEqualConstraint (SFloat n) (SFloat m)  = return $ n .<= m
approximatedByOrEqualConstraint SPoint SPoint          = return $ sTrue
approximatedByOrEqualConstraint (SExtNat x) (SExtNat y) = return $ x .== y
approximatedByOrEqualConstraint (SOOZ s) (SOOZ r) = pure $ s .== r
approximatedByOrEqualConstraint (SSet s) (SSet t) = pure $ s `S.isSubsetOf` t

approximatedByOrEqualConstraint (SLevel l) (SLevel k) =
    -- Private <= Public
  return
    $ ite (l .== literal unusedRepresentation) sTrue
      $ ite (l .== literal privateRepresentation) sTrue
        $ ite (k .== literal publicRepresentation) sTrue sFalse

approximatedByOrEqualConstraint (SSec a) (SSec b) =
  -- Lo <= Lo   (False <= False)
  -- Hi <= Hi   (True <= True)
  -- Hi <= Lo   (True <= False)
  -- but not Lo <= Hi   (False  <= True)
  -- So this is flipped implication
  return (b .=> a)

approximatedByOrEqualConstraint (SLNL a) (SLNL b) =
  -- Lin (F) <= NonLin (T)
  -- but not (NonLin (T) <= Lin (F))
  return (a .=> b)

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

approximatedByOrEqualConstraint s1 s2@(SInterval _ _) =
  approximatedByOrEqualConstraint (SInterval s1 s1) s2

approximatedByOrEqualConstraint s1@(SInterval _ _) s2 =
  approximatedByOrEqualConstraint s1 (SInterval s2 s2)

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
        predFold concat (\_ -> []) (\_ _ q -> q) (\x -> [x]) id (\_ _ p -> p)

    -- All the (trivially) unsatisfiable constraints
    unsat :: Constraint -> [Constraint]
    unsat c@(Eq _ c1 c2 _)  = if (normalise c1 `neqC` normalise c2) then [c] else []
    unsat c@(Neq _ c1 c2 _) = if (normalise c1 `neqC` normalise c2) then [] else [c]
    unsat c@(ApproximatedBy s c1 c2 t) =
        approximatedByC (ApproximatedBy s (normalise c1) (normalise c2) t)
    -- TODO: look at this information
    unsat Lub{} = []
    unsat (Lt _ c1 c2) = []
    unsat (Gt _ c1 c2) = []
    unsat (LtEq _ c1 c2) = []
    unsat (GtEq _ c1 c2) = []

    -- TODO: unify this with eqConstraint and approximatedByOrEqualConstraint
    -- Attempt to see if one coeffect is trivially greater than the other
    approximatedByC :: Constraint -> [Constraint]
    approximatedByC c@(ApproximatedBy s (TySig r t) (TySig r' t') tm) | t == t' =
      approximatedByC (ApproximatedBy s r r' tm)
    approximatedByC c@(ApproximatedBy s (TySig r t) r' tm) =
      approximatedByC (ApproximatedBy s r r' tm)
    approximatedByC c@(ApproximatedBy s r (TySig r' t') tm) =
      approximatedByC (ApproximatedBy s r r' tm)
    approximatedByC c@(ApproximatedBy _ (TyInt n) (TyInt m) _) | n /= m = [c]
    approximatedByC c@(ApproximatedBy _ (TyCon (internalName -> "Public")) (TyCon (internalName -> "Private")) _) = [c]
    approximatedByC c@(ApproximatedBy _ (TyRational n) (TyRational m) _) | n > m = [c]
    -- Nat like intervals
    approximatedByC c@(ApproximatedBy _
                        (TyInfix TyOpInterval (TyInt lb1) (TyInt ub1))
                        (TyInfix TyOpInterval (TyInt lb2) (TyInt ub2)) _)
        | not $ (lb2 <= lb1) && (ub1 <= ub2) = [c]

    approximatedByC (ApproximatedBy s (isProduct -> Just (c1, c2)) (isProduct -> Just (d1, d2)) (isProduct -> Just (t1, t2))) =
      (approximatedByC (ApproximatedBy s c1 d1 t1)) ++ (approximatedByC (ApproximatedBy s c2 d2 t2))

    approximatedByC (ApproximatedBy s c (isProduct -> Just (d1, d2)) (isProduct -> Just (t1, t2))) =
      (approximatedByC (ApproximatedBy s c d1 t1)) ++ (approximatedByC (ApproximatedBy s c d2 t2))

    approximatedByC (ApproximatedBy s (isProduct -> Just (c1, c2)) d (isProduct -> Just (t1, t2))) =
      (approximatedByC (ApproximatedBy s c1 d t1)) ++ (approximatedByC (ApproximatedBy s c2 d t2))

    approximatedByC _ = []

    -- Attempt to see if one coeffect is trivially not equal to the other
    neqC :: Type -> Type -> Bool
    neqC (TyInt n) (TyInt m) = n /= m
    neqC (TyRational n) (TyRational m) = n /= m
    --neqC (CInterval lb1 ub1) (CInterval lb2 ub2) =
    --   neqC lb1 lb2 || neqC ub1 ub2
    neqC (TySig r t) (TySig r' t') | t == t' = neqC r r'
    neqC (TySig r t) r' = neqC r r'
    neqC r (TySig r' t) = neqC r r'
    neqC _ _            = False

data SolverResult
  = QED
  | NotValid String
  | NotValidTrivial [Constraint]
  | Timeout
  | SolverProofError String
  | OtherSolverError String

provePredicate
  :: (?globals :: Globals)
  => Pred                        -- Predicate
  -> Ctxt (Type, Quantifier) -- Free variable quantifiers
  -> IO (Double, SolverResult)
provePredicate predicate vars
  | isTrivial predicate = do
      debugM "solveConstraints" "Skipping solver because predicate is trivial."
      return (0.0, QED)
  | otherwise = do
      let (sbvTheorem, _, unsats) = compileToSBV predicate vars

      -- Benchmarking start
      start  <- if benchmarking then Clock.getTime Clock.Monotonic else return 0
      -- Prove -----------
      ThmResult thmRes <- proveWith defaultSMTCfg $ do --  -- proveWith cvc4 {verbose=True}
        case solverTimeoutMillis of
          n | n <= 0 -> return ()
          n -> setTimeOut n
        sbvTheorem
      ------------------
      -- Benchmarking end
      -- Force the result
      _ <- return $ thmRes `seq` thmRes
      end    <- if benchmarking then Clock.getTime Clock.Monotonic else return 0
      let duration = (fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double))

      return $ (duration, case thmRes of
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
            Left str -> OtherSolverError str)

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

matchTypes :: MonadIO m => Type -> Maybe Type -> m Type
matchTypes t Nothing = return t
matchTypes t (Just t') | t == t' = return t
matchTypes t (Just t') | otherwise = solverError $ "I have conflicting kinds of " ++ show t ++ " and " ++ show t'
