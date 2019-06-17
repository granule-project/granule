{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}


{- Deals with compilation of coeffects into symbolic representations of SBV -}

module Language.Granule.Checker.Constraints where

import Data.Foldable (foldrM)
import Data.List (isPrefixOf)
import Data.SBV hiding (kindOf, name, symbolic)
import qualified Data.Set as S
import Control.Arrow (first)
import Control.Exception (assert)

import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Kinds
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

-- | Compile constraint into an SBV symbolic bool, along with a list of
-- | constraints which are trivially unequal (if such things exist) (e.g., things like 1=0).
compileToSBV :: (?globals :: Globals)
  => Pred -> Ctxt (Type, Quantifier)
  -> (Symbolic SBool, Symbolic SBool, [Constraint])
compileToSBV predicate tyVarContext =
  (buildTheorem id compileQuant
  , undefined -- buildTheorem sNot (compileQuant . flipQuant)
  , trivialUnsatisfiableConstraints predicate')

  where
    -- flipQuant ForallQ   = InstanceQ
    -- flipQuant InstanceQ = ForallQ
    -- flipQuant BoundQ    = BoundQ

    predicate' = rewriteConstraints tyVarContext predicate

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
            Just t | t == extendedNat ->
                  forSome [internalName v] $ \solverVar -> do
                    pred' <- buildTheorem' ((v, SExtNat (SNatX solverVar)) : solverVars) p
                    return ((SNatX.representationConstraint solverVar) .&& pred')

            Just (TyCon k) ->
                  case internalName k of
                    "Q" ->
                      forSome [internalName v] $ \solverVar ->
                        buildTheorem' ((v, SFloat solverVar) : solverVars) p

                    -- Esssentially a stub for sets at this point
                    "Set" -> buildTheorem' ((v, SSet S.empty) : solverVars) p

                    "Nat" ->
                      forSome [(internalName v)] $ \solverVar -> do
                        pred' <- buildTheorem' ((v, SNat solverVar) : solverVars) p
                        return (solverVar .>= 0 .&& pred')

                    "Level" ->
                       forSome [(internalName v)] $ \solverVar -> do
                         pred' <- buildTheorem' ((v, SLevel solverVar) : solverVars) p
                         return ((solverVar .== literal privateRepresentation
                              .|| solverVar .== literal publicRepresentation) .&& pred')

                    k -> error $ "Solver error: I don't know how to create an existntial for " <> show k
            Just k -> error $ "Solver error: I don't know how to create an existntial for demotable type " <> show k

            Nothing ->
              case k of
                KType -> buildTheorem' solverVars p
                _ -> error $ "Trying to make a fresh existential solver variable for a grade of kind: "
                             <> show k <> " but I don't know how."
        else
          buildTheorem' solverVars p

    -- TODO: generalise this to not just Nat indices
    buildTheorem' solverVars (Impl ((v, _kind):vs) p p') =
      if v `elem` (freeVars p <> freeVars p')
        -- If the quantified variable appears in the theorem
        then

          -- Create fresh solver variable
          forAll [(internalName v)] $ \vSolver -> do
             impl <- buildTheorem' ((v, SNat vSolver) : solverVars) (Impl vs p p')
             return ((vSolver .>= literal 0) .=> impl)

        else
          -- An optimisation, don't bother quantifying things
          -- which don't appear in the theorem anyway

          buildTheorem' solverVars (Impl vs p p')

    buildTheorem' solverVars (Con cons) =
      compile solverVars cons

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
         let (universalConstraints', existentialConstraints') =
               case quantifierType of
                 ForallQ -> (pre .&& universalConstraints, existentialConstraints)
                 InstanceQ -> (universalConstraints, pre .&& existentialConstraints)
                 b -> error $ "Impossible freshening a BoundQ, but this is cause above"
             --    BoundQ -> (universalConstraints, pre .&& existentialConstraints)
         return (universalConstraints', existentialConstraints', (var, symbolic) : ctxt)

-- TODO: replace with use of `substitute`

-- given an context mapping coeffect type variables to coeffect typ,
-- then rewrite a set of constraints so that any occruences of the kind variable
-- are replaced with the coeffect type
rewriteConstraints :: Ctxt (Type, Quantifier) -> Pred -> Pred
rewriteConstraints ctxt =
    predFold
      Conj
      Disj
      Impl
      (\c -> Con $ foldr (uncurry updateConstraint) c ctxt)
      NegPred
      existsCase
  where
    existsCase :: Id -> Language.Granule.Syntax.Type.Kind -> Pred -> Pred
    existsCase var (KVar kvar) p =
      Exists var k' p
        where
          k' = case lookup kvar ctxt of
                  Just (ty, _) -> KPromote ty
                  Nothing -> KVar kvar
    existsCase var k p = Exists var k p

    -- `updateConstraint v k c` rewrites any occurence of the kind variable
    -- `v` in the constraint `c` with the kind `k`
    updateConstraint :: Id -> (Type, Quantifier) -> Constraint -> Constraint
    updateConstraint ckindVar (ckind, _) (Eq s c1 c2 k) =
      Eq s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
        (case k of
          TyVar ckindVar' | ckindVar == ckindVar' -> ckind
          _ -> k)
    updateConstraint ckindVar (ckind, _) (Neq s c1 c2 k) =
            Neq s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
              (case k of
                TyVar ckindVar' | ckindVar == ckindVar' -> ckind
                _ -> k)

    updateConstraint ckindVar (ckind, _) (ApproximatedBy s c1 c2 k) =
      ApproximatedBy s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
        (case k of
          TyVar ckindVar' | ckindVar == ckindVar' -> ckind
          _  -> k)

    updateConstraint ckindVar (ckind, _) (NonZeroPromotableTo s x c t) =
       NonZeroPromotableTo s x (updateCoeffect ckindVar ckind c)
          (case t of
             TyVar ckindVar' | ckindVar == ckindVar' -> ckind
             _  -> t)

    updateConstraint ckindVar (ckind, _) (Lt s c1 c2) =
        Lt s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)

    updateConstraint ckindVar (ckind, _) (Gt s c1 c2) =
        Gt s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)


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
    updateCoeffect ckindVar ckind (CMinus c1 c2) =
      CMinus (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CExpon c1 c2) =
      CExpon (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CInterval c1 c2) =
      CInterval (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect _ _ c = c


-- | Symbolic coeffect representing 0..Inf
zeroToInfinity :: SGrade
zeroToInfinity = SInterval (SExtNat $ SNatX 0) (SExtNat SNatX.inf)


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
              .|| solverVar .== literal publicRepresentation, SLevel solverVar)

        k -> do
           error $ "I don't know how to make a fresh solver variable of type " <> show k

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
  error $ "Trying to make a fresh solver variable for a grade of type: "
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
        "Level"     -> SLevel $ literal privateRepresentation
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
approximatedByOrEqualConstraint (SLevel l) (SLevel k) = l .>= k
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
    = filter unsat
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

    unsat :: Constraint -> Bool
    unsat (Eq _ c1 c2 _)  = c1 `neqC` c2
    unsat (Neq _ c1 c2 _) = not (c1 `neqC` c2)
    unsat (ApproximatedBy _ c1 c2 _) = c1 `approximatedByC` c2
    unsat (NonZeroPromotableTo _ _ (CZero _) _) = True
    unsat (NonZeroPromotableTo _ _ _ _) = False
    -- TODO: look at this information
    unsat (Lt _ c1 c2) = False
    unsat (Gt _ c1 c2) = False

    -- TODO: unify this with eqConstraint and approximatedByOrEqualConstraint
    -- Attempt to see if one coeffect is trivially greater than the other
    approximatedByC :: Coeffect -> Coeffect -> Bool
    approximatedByC (CNat n) (CNat m) = n /= m
    approximatedByC (Level n) (Level m)   = n < m
    approximatedByC (CFloat n) (CFloat m) = n > m
    -- Nat like intervals
    approximatedByC (CInterval (CNat lb1) (CNat ub1)) (CInterval (CNat lb2) (CNat ub2)) =
        not $ (lb2 <= lb1) && (ub1 <= ub2)
    approximatedByC _ _                   = False

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
