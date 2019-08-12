{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}


{- Deals with compilation of coeffects into symbolic representations of SBV -}

module Language.Granule.Checker.Constraints where

--import Data.Foldable (foldrM)
import Data.List (isPrefixOf)
import Data.SBV hiding (kindOf, name, symbolic)
import qualified Data.Set as S
import Control.Arrow (first)
import Control.Exception (assert)
import Control.Monad.IO.Class
import System.Exit

import Language.Granule.Checker.Predicates
import Language.Granule.Context (Ctxt)

import Language.Granule.Checker.Constraints.SymbolicGrades
import Language.Granule.Checker.Constraints.Quantifiable
import Language.Granule.Checker.Constraints.SNatX (SNatX(..))
import qualified Language.Granule.Checker.Constraints.SNatX as SNatX

import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type
import Language.Granule.Utils

-- | What is the SBV represnetation of a quantifier
compileQuant :: Quantifiable a => Quantifier -> (String -> Symbolic a)
compileQuant ForallQ   = universal
compileQuant InstanceQ = existential
compileQuant BoundQ    = existential

compileQuantScoped :: QuantifiableScoped a => Quantifier -> String -> (SBV a -> Symbolic SBool) -> Symbolic SBool
compileQuantScoped ForallQ = universalScoped
compileQuantScoped _ = existentialScoped

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
      freshCVarScoped compileQuantScoped (internalName v) t q
         (\(varPred, solverVar) -> do
             pred <- buildTheoremNew ctxt ((v, solverVar) : solverVars)
             case q of
              ForallQ -> return $ varPred .=> pred
              _       -> return $ varPred .&& pred)
{-
    buildTheorem ::
        (SBool -> SBool)
     -> (forall a. Quantifiable a => Quantifier -> (String -> Symbolic a))
     -> Symbolic SBool
    buildTheorem polarity quant = do
      -- Create fresh solver variables for everything in the type variable
      -- context of the write kind

      -- IMPORTANT: foldrM creates its side effects in reverse order
      -- this is good because tyVarContext has the reverse order for our
      -- quantifiers, so reversing order of the effects in foldrM gives us
      -- the order we want for the predicate
        (preConstraints, constraints, solverVars) <-
            foldrM (createFreshVar quant predicate) (sTrue, sTrue, []) tyVarContext

        predC <- buildTheorem' solverVars predicate'
        return (polarity (preConstraints .=> (constraints .&& predC)))
-}
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
          case demoteKindToType k of
            Just t ->
              freshCVarScoped compileQuantScoped (internalName v) t InstanceQ
                (\(varPred, solverVar) -> do
                  pred' <- buildTheorem' ((v, solverVar) : solverVars) p
                  return (varPred .&& pred'))

            Nothing ->
              case k of
                KType -> buildTheorem' solverVars p
                _ ->
                  solverError $ "Trying to make a fresh existential solver variable for a grade of kind: "
                             <> show k <> " but I don't know how."
        else
          buildTheorem' solverVars p

    -- TODO: generalise this to not just Nat indices
    buildTheorem' solverVars (Impl ((v, k):vs) p p') =
      if v `elem` (freeVars p <> freeVars p')
        -- If the quantified variable appears in the theorem
        then
          case demoteKindToType k of
            Just t ->
              freshCVarScoped compileQuantScoped (internalName v) t ForallQ
                (\(varPred, solverVar) -> do
                  pred' <- buildTheorem' ((v, solverVar) : solverVars) (Impl vs p p')
                  return (varPred .=> pred'))
            Nothing ->
                    case k of
                      KType -> buildTheorem' solverVars p
                      _ -> error $ "Trying to make a fresh universal solver variable for a grade of kind: "
                                   <> show k <> " but I don't know how."

        else
          -- An optimisation, don't bother quantifying things
          -- which don't appear in the theorem anyway

          buildTheorem' solverVars (Impl vs p p')

    buildTheorem' solverVars (Con cons) =
      compile solverVars cons
{-
    -- Create a fresh solver variable of the right kind and
    -- with an associated refinement predicate
    createFreshVar
      :: (forall a. Quantifiable a => Quantifier -> (String -> Symbolic a))
      -> Pred
      -> (Id, (Type, Quantifier))
      -> (SBool, SBool, Ctxt SGrade)
      -> Symbolic (SBool, SBool, Ctxt SGrade)
    -- Ignore variables coming from a dependent pattern match because
    -- they get created elsewhere

    createFreshVar _ _ (_, (_, BoundQ)) x = return x

    createFreshVar quant predicate
                   (var, (kind, quantifierType))
                   (universalConstraints, existentialConstraints, ctxt) =
      if not (var `elem` (freeVars predicate))
        -- If the variable is not in the predicate, then don't create a new var
        then return (universalConstraints, existentialConstraints, ctxt)

        -- Otherwise...
        else do
         (pre, symbolic) <- freshCVar quant (internalName var) kind quantifierType
         (universalConstraints', existentialConstraints') <-
               case quantifierType of
                 ForallQ -> return (pre .&& universalConstraints, existentialConstraints)
                 InstanceQ -> return (universalConstraints, pre .&& existentialConstraints)
                 b -> solverError $ "Impossible freshening a BoundQ, but this is cause above"
             --    BoundQ -> (universalConstraints, pre .&& existentialConstraints)
         return (universalConstraints', existentialConstraints', (var, symbolic) : ctxt)
-}

-- | Symbolic coeffect representing 0..Inf
zeroToInfinity :: SGrade
zeroToInfinity = SInterval (SExtNat $ SNatX 0) (SExtNat SNatX.inf)

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
       (\(predUb, solverVarUb) ->
          -- Respect the meaning of intervals
          k ( predLb .&& predUb .&& solverVarUb .>= solverVarLb
            , SInterval solverVarLb solverVarUb
          )))

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
        k -> error $ "I don't know how to make a fresh solver variable of type " <> show conName)

freshCVarScoped quant name t q k | t == extendedNat = do
  quant q name (\solverVar ->
    k (SNatX.representationConstraint solverVar
     , SExtNat (SNatX solverVar)))

-- A poly typed coeffect variable compiled into the
--  infinity value (since this satisfies all the semiring properties on the nose)
freshCVarScoped quant name (TyVar v) q k | "kprom" `isPrefixOf` internalName v =
-- future TODO: resolve polymorphism to free coeffect (uninterpreted)
  k (sTrue, SPoint)

freshCVarScoped quant name (TyVar v) q k =
  quant q name (\solverVar -> k (sTrue, SUnknown $ SynLeaf $ Just solverVar))

freshCVarScoped _ _ t _ _ =
  error $ "Trying to make a fresh solver variable for a grade of type: "
      <> show t <> " but I don't know how."

-- | Generate a solver variable of a particular kind, along with
-- a refinement predicate
freshCVar :: (forall a . Quantifiable a => Quantifier -> (String -> Symbolic a))
          -> String -> Type -> Quantifier -> Symbolic (SBool, SGrade)

freshCVar quant name (isInterval -> Just t) q = do
  -- Interval, therefore recursively generate fresh vars for the lower and upper
  (predLb, solverVarLb) <- freshCVar quant (name <> ".lower") t q
  (predUb, solverVarUb) <- freshCVar quant (name <> ".upper") t q
  -- constrain (predLb .&& predUb .&& solverVarUb .>= solverVarLb)
  return
     -- Respect the meaning of intervals
    ( predLb .&& predUb .&& solverVarUb .>= solverVarLb
    , SInterval solverVarLb solverVarUb
    )

freshCVar quant name (isProduct -> Just (t1, t2)) q = do
  -- Product, therefore recursively generate fresh vars for the lower and upper
  (predLb, solverVarFst) <- freshCVar quant (name <> ".fst") t1 q
  (predUb, solverVarSnd) <- freshCVar quant (name <> ".snd") t2 q
  return (sTrue, SProduct solverVarFst solverVarSnd)

freshCVar quant name (TyCon k) q =
  case internalName k of
    -- Floats (rationals)
    "Q" -> do
      solverVar <- quant q name
      return (sTrue, SFloat solverVar)

    -- Esssentially a stub for sets at this point
    "Set"       -> return (sTrue, SSet S.empty)

    _ -> do -- Otherwise it must be an SInteger-like constraint:
      solverVar <- quant q name
      case internalName k of
        "Nat"       -> do
          -- constrain (solverVar .>= 0)
          return (solverVar .>= 0, SNat solverVar)

        "Level"     -> do
          -- constrain (solverVar .== 0 .|| solverVar .== 1)
          return (solverVar .== literal privateRepresentation
              .|| solverVar .== literal publicRepresentation
              .|| solverVar .== literal unusedRepresentation, SLevel solverVar)

        k -> do
          solverError $ "I don't know how to make a fresh solver variable of type " <> show k

-- Extended nat
freshCVar quant name t q | t == extendedNat = do
  solverVar <- quant q name
  -- constrain (SNatX.representationConstraint $ SNatX.xVal solverVar)
  return (SNatX.representationConstraint $ SNatX.xVal solverVar
        , SExtNat solverVar)

-- A poly typed coeffect variable compiled into the
--  infinity value (since this satisfies all the semiring properties on the nose)
freshCVar quant name (TyVar v) q | "kprom" `isPrefixOf` internalName v = do
-- future TODO: resolve polymorphism to free coeffect (uninterpreted)
  return (sTrue, SPoint)

freshCVar quant name (TyVar v) q = do
  solverVar <- quant q name
  return (sTrue, SUnknown $ SynLeaf $ Just solverVar)

freshCVar _ _ t _ =
  solverError $ "Trying to make a fresh solver variable for a grade of type: "
   <> show t <> " but I don't know how."

-- Compile a constraint into a symbolic bool (SBV predicate)
compile :: (?globals :: Globals) =>
  Ctxt SGrade -> Constraint -> Symbolic SBool
compile vars (Eq _ c1 c2 t) =
  return $ eqConstraint c1' c2'
    where
      c1' = compileCoeffect c1 t vars
      c2' = compileCoeffect c2 t vars
compile vars (Neq _ c1 c2 t) =
   return $ sNot (eqConstraint c1' c2')
  where
    c1' = compileCoeffect c1 t vars
    c2' = compileCoeffect c2 t vars
compile vars (ApproximatedBy _ c1 c2 t) =
  return $ approximatedByOrEqualConstraint c1' c2'
    where
      c1' = compileCoeffect c1 t vars
      c2' = compileCoeffect c2 t vars

compile vars (Lt s c1 c2) =
  return $ c1' .< c2'
  where
    c1' = compileCoeffect c1 (TyCon $ mkId "Nat") vars
    c2' = compileCoeffect c2 (TyCon $ mkId "Nat") vars

compile vars (Gt s c1 c2) =
  return $ c1' .> c2'
  where
    c1' = compileCoeffect c1 (TyCon $ mkId "Nat") vars
    c2' = compileCoeffect c2 (TyCon $ mkId "Nat") vars

compile vars (LtEq s c1 c2) =
  return $ c1' .<= c2'
  where
    c1' = compileCoeffect c1 (TyCon $ mkId "Nat") vars
    c2' = compileCoeffect c2 (TyCon $ mkId "Nat") vars

compile vars (GtEq s c1 c2) =
  return $ c1' .>= c2'
  where
    c1' = compileCoeffect c1 (TyCon $ mkId "Nat") vars
    c2' = compileCoeffect c2 (TyCon $ mkId "Nat") vars


-- NonZeroPromotableTo s c means that:
compile vars (NonZeroPromotableTo s x c t) = do
  -- exists x .
  (req, xVar) <- freshCVar compileQuant (internalName x) t InstanceQ

  -- x != 0
  nonZero <- compile ((x, xVar) : vars) (Neq s (CZero t) (CVar x) t)

  -- x * 1 == c
  promotableToC <- compile ((x, xVar) : vars) (Eq s (CTimes (COne t) (CVar x)) c t)

  return (req .&& nonZero .&& promotableToC)


-- | Compile a coeffect term into its symbolic representation
compileCoeffect :: (?globals :: Globals) =>
  Coeffect -> Type -> [(Id, SGrade)] -> SGrade

compileCoeffect (CSig c k) _ ctxt = compileCoeffect c k ctxt

-- Trying to compile a coeffect from a promotion that was never
-- constrained further: default to the cartesian coeffect
-- future TODO: resolve polymorphism to free coeffect (uninterpreted)
compileCoeffect c (TyVar v) _ | "kprom" `isPrefixOf` internalName v = SPoint

compileCoeffect (Level n) (TyCon k) _ | internalName k == "Level" =
  SLevel . fromInteger . toInteger $ n

compileCoeffect (Level n) (isProduct -> Just (TyCon k, t2)) vars | internalName k == "Level" =
  SProduct (SLevel . fromInteger . toInteger $ n) (compileCoeffect (COne t2) t2 vars)

compileCoeffect (Level n) (isProduct -> Just (t1, TyCon k)) vars | internalName k == "Level" =
  SProduct (compileCoeffect (COne t1) t1 vars) (SLevel . fromInteger . toInteger $ n)

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
    _ -> error $ "Looking up a variable '" <> show v <> "' in " <> show vars

compileCoeffect c@(CMeet n m) k vars =
  (compileCoeffect n k vars) `symGradeMeet` (compileCoeffect m k vars)

compileCoeffect c@(CJoin n m) k vars =
  (compileCoeffect n k vars) `symGradeJoin` (compileCoeffect m k vars)

compileCoeffect c@(CPlus n m) k vars =
  (compileCoeffect n k vars) `symGradePlus` (compileCoeffect m k vars)

compileCoeffect c@(CTimes n m) k vars =
  (compileCoeffect n k vars) `symGradeTimes` (compileCoeffect m k vars)

compileCoeffect c@(CMinus n m) k vars =
  (compileCoeffect n k vars) `symGradeMinus` (compileCoeffect m k vars)

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
        "Level"     -> SLevel $ literal unusedRepresentation
        "Nat"       -> SNat 0
        "Q"         -> SFloat (fromRational 0)
        "Set"       -> SSet (S.fromList [])
        _           -> error $ "I don't know how to compile a 0 for " <> pretty k'
    (otherK', otherK) | (otherK' == extendedNat || otherK' == nat) && otherK == extendedNat ->
      SExtNat 0

    (isProduct -> Just (t1, t2), isProduct -> Just (t1', t2')) ->
      SProduct
        (compileCoeffect (CZero t1) t1' vars)
        (compileCoeffect (CZero t2) t2' vars)

    (isInterval -> Just t, isInterval -> Just t') ->
      SInterval
        (compileCoeffect (CZero t) t' vars)
        (compileCoeffect (CZero t) t' vars)

    (TyVar _, _) -> SUnknown (SynLeaf (Just 0))
    _ -> error $ "I don't know how to compile a 0 for " <> pretty k'

compileCoeffect (COne k') k vars =
  case (k', k) of
    (TyCon k', TyCon k) -> assert (internalName k' == internalName k) $
      case internalName k' of
        "Level"     -> SLevel $ literal privateRepresentation
        "Nat"       -> SNat 1
        "Q"         -> SFloat (fromRational 1)
        "Set"       -> SSet (S.fromList [])
        _           -> error $ "I don't know how to compile a 1 for " <> pretty k'

    (otherK', otherK) | (otherK' == extendedNat || otherK' == nat) && otherK == extendedNat ->
      SExtNat 1

    (isProduct -> Just (t1, t2), isProduct -> Just (t1', t2')) ->
      SProduct
        (compileCoeffect (COne t1) t1' vars)
        (compileCoeffect (COne t2) t2' vars)

    -- Build an interval for 1
    (isInterval -> Just t, isInterval -> Just t') ->
        SInterval
          (compileCoeffect (COne t) t' vars)
          (compileCoeffect (COne t) t' vars)
    (TyVar _, _) -> SUnknown (SynLeaf (Just 1))

    _ -> error $ "I don't know how to compile a 1 for " <> pretty k'

compileCoeffect (CProduct c1 c2) (isProduct -> Just (t1, t2)) vars =
  SProduct (compileCoeffect c1 t1 vars) (compileCoeffect c2 t2 vars)

-- For grade-polymorphic coeffects, that have come from a nat
-- expression (sometimes this is just from a compounded expression of 1s),
-- perform the injection from Natural numbers to arbitrary semirings
compileCoeffect (CNat n) (TyVar _) _ | n > 0 =
  SUnknown (injection n)
    where
      injection 0 = SynLeaf (Just 0)
      injection 1 = SynLeaf (Just 1)
      injection n = SynPlus (SynLeaf (Just 1)) (injection (n-1))

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
  (eqConstraint lb1 lb2) .&& (eqConstraint ub1 ub2)
eqConstraint (SExtNat x) (SExtNat y) = x .== y
eqConstraint SPoint SPoint = sTrue
eqConstraint s t | isSProduct s && isSProduct t =
  applyToProducts (.==) (.&&) (const sTrue) s t
eqConstraint u@(SUnknown{}) u'@(SUnknown{}) =
  u .== u'
eqConstraint x y =
   error $ "Kind error trying to generate equality " <> show x <> " = " <> show y

-- | Generate less-than-equal constraints for two symbolic coeffects
approximatedByOrEqualConstraint :: SGrade -> SGrade -> SBool
approximatedByOrEqualConstraint (SNat n) (SNat m) = n .== m
approximatedByOrEqualConstraint (SFloat n) (SFloat m)   = n .<= m
approximatedByOrEqualConstraint (SLevel l) (SLevel k) =
    -- Private <= Public
    ite (l .== literal unusedRepresentation) sTrue
      $ ite (l .== literal privateRepresentation) sTrue
        $ ite (k .== literal publicRepresentation) sTrue sFalse
approximatedByOrEqualConstraint (SSet s) (SSet t) =
  if s == t then sTrue else sFalse
approximatedByOrEqualConstraint SPoint SPoint = sTrue

approximatedByOrEqualConstraint s t | isSProduct s && isSProduct t =
  applyToProducts approximatedByOrEqualConstraint (.&&) (const sTrue) s t

-- Perform approximation when nat-like grades are involved
approximatedByOrEqualConstraint (SInterval lb1 ub1) (SInterval lb2 ub2)
    | natLike lb1 && natLike lb2 && natLike ub1 && natLike ub2 =
      (lb2 .<= lb1) .&& (ub1 .<= ub2)

-- if intervals are not nat-like then use the notion of approximation
-- given here
approximatedByOrEqualConstraint (SInterval lb1 ub1) (SInterval lb2 ub2) =
  (approximatedByOrEqualConstraint lb2 lb1)
     .&& (approximatedByOrEqualConstraint ub1 ub2)

approximatedByOrEqualConstraint (SExtNat x) (SExtNat y) = x .== y

approximatedByOrEqualConstraint u@(SUnknown{}) u'@(SUnknown{}) =
     -- Note shortcircuiting version of || implemented here
     ite (u .== u') sTrue (u .< u')

approximatedByOrEqualConstraint x y =
   error $ "Kind error trying to generate " <> show x <> " <= " <> show y


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

    -- All the unsatisfiable constraints
    unsat :: Constraint -> [Constraint]
    unsat c@(Eq _ c1 c2 _)  = if (c1 `neqC` c2) then [c] else []
    unsat c@(Neq _ c1 c2 _) = if (c1 `neqC` c2) then [] else [c]
    unsat c@(ApproximatedBy{}) = approximatedByC c
    unsat c@(NonZeroPromotableTo _ _ (CZero _) _) = [c]
    unsat (NonZeroPromotableTo _ _ _ _) = []
    -- TODO: look at this information
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
  -> Ctxt (Type, Quantifier) -- Free variable quantifiers
  -> IO SolverResult
provePredicate predicate vars
  | isTrivial predicate = do
      debugM "solveConstraints" "Skipping solver because predicate is trivial."
      return QED
  | otherwise = do
      let (sbvTheorem, _, unsats) = compileToSBV predicate vars
      ThmResult thmRes <- prove $ do -- proveWith defaultSMTCfg {verbose=True}
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

solverError :: MonadIO m => String -> m a
solverError msg = liftIO $ do
  putStrLn msg
  exitFailure