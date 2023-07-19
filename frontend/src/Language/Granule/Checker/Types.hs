{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

-- | Type equality (and inequalities when grades are involved)
module Language.Granule.Checker.Types where

import Control.Monad.State.Strict
import Data.List (sortBy, sort)

import Language.Granule.Checker.Effects
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Kinding
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Normalise

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Helpers (freeVars)
import Language.Granule.Utils
import Language.Granule.Context

import Data.Functor.Const

lEqualTypesWithPolarity :: (?globals :: Globals)
  => Span -> SpecIndicator -> Type -> Type -> Checker (Bool, Type, Substitution)
lEqualTypesWithPolarity s pol t1 t2 = do
  let (t1', t2') = if pol == SndIsSpec then (t1, t2) else (t2, t1)
  equalTypesRelatedCoeffectsAndUnify s ApproximatedBy pol t1' t2'

equalTypesWithPolarity :: (?globals :: Globals)
  => Span -> SpecIndicator -> Type -> Type -> Checker (Bool, Type, Substitution)
equalTypesWithPolarity s pol t1 t2 = do
  let (t1', t2') = if pol == SndIsSpec then (t1, t2) else (t2, t1)
  equalTypesRelatedCoeffectsAndUnify s Eq pol t1' t2'

lEqualTypes :: (?globals :: Globals)
  => Span -> Type -> Type -> Checker (Bool, Type, Substitution)
lEqualTypes s = equalTypesRelatedCoeffectsAndUnify s ApproximatedBy SndIsSpec

equalTypes :: (?globals :: Globals)
  => Span -> Type -> Type -> Checker (Bool, Type, Substitution)
equalTypes s = equalTypesRelatedCoeffectsAndUnify s Eq SndIsSpec

--- Flags

data SpecIndicator = FstIsSpec | SndIsSpec | PatternCtxt
  deriving (Eq, Show)

data Mode = Types | Effects deriving Show

-- Abstracted equality/relation on grades
relGrades :: (?globals :: Globals)
  => Span -> Coeffect -> Coeffect
  -- Explain how coeffects should be related by a solver constraint
  -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
  -> Checker Substitution
relGrades s c c' rel = do
  -- Unify the coeffect kinds of the two coeffects
  (kind, subst, (inj1, inj2)) <- mguCoeffectTypesFromCoeffects s c c'

  -- Add constraint for the coeffect (using ^op for the ordering compared with the order of equality)
  c' <- substitute subst c'
  c  <- substitute subst c
  kind <- substitute subst kind
  addConstraint (rel s (inj2 c') (inj1 c) kind)
  debugM "added solver constraint from box-types equality" (pretty $ (rel s (inj2 c') (inj1 c) kind))
  return subst

{- | Check whether two types are equal, and at the same time
     generate (in)equality constraints and perform unification (on non graded things)

     The first argument is taken to be possibly approximated by the second
     e.g., the first argument is inferred, the second is a specification being
     checked against.
-}
equalTypesRelatedCoeffectsAndUnify :: (?globals :: Globals)
  => Span
  -- Explain how coeffects should be related by a solver constraint
  -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
  -- Starting spec indication
  -> SpecIndicator
  -- Left type (may be approximated by right type)
  -> Type
  -- Right type
  -> Type
-- Result is a effectful, producing:
  --    * a boolean of the equality
  --    * the most specialised type (after the unifier is applied)
  --    * the unifier
  -> Checker (Bool, Type, Substitution)
equalTypesRelatedCoeffectsAndUnify s rel spec t1 t2 = do
   (eq, unif) <- equalTypesRelatedCoeffects s rel (normaliseType t1) (normaliseType t2) spec Types
   if eq
     then do
        t2 <- substitute unif t2
        return (eq, t2, unif)
     else let t1 = normaliseType t1 in
       return (eq, t1, [])

flipIndicator :: SpecIndicator -> SpecIndicator
flipIndicator FstIsSpec = SndIsSpec
flipIndicator SndIsSpec = FstIsSpec
flipIndicator PatternCtxt = PatternCtxt

{- | Check whether two types are equal, and at the same time
     generate coeffect equality constraints and a unifier
      Polarity indicates which -}
equalTypesRelatedCoeffects :: (?globals :: Globals)
  => Span
  -- Explain how coeffects should be related by a solver constraint
  -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
  -> Type
  -> Type
  -- Indicates whether the first type or second type is a specification
  -> SpecIndicator
  -- Flag to say whether this type is really a type or an effect
  -> Mode
  -> Checker (Bool, Substitution)
equalTypesRelatedCoeffects s rel t1 t2 spec mode = do
  -- Infer kinds
  (k, subst, _) <- synthKind s t1
  -- check the other type has the same kind
  (subst', _) <- checkKind s t2 k
  substFromK <- combineManySubstitutions s [subst,subst']
  -- apply substitutions before equality
  t1 <- substitute substFromK t1
  t2 <- substitute substFromK t2
  -- main equality
  (eqT, subst'') <- equalTypesRelatedCoeffectsInner s rel t1 t2 k spec mode
  substFinal <- combineManySubstitutions s [substFromK, subst'']
  return (eqT, substFinal)

-- Check if `t1 == t2` at kind `k`
equalTypesRelatedCoeffectsInner :: (?globals :: Globals)
  => Span
  -- Explain how coeffects should be related by a solver constraint
  -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
  -> Type -- t1
  -> Type -- t2
  -> Type -- k - Kind parameter
  -- Indicates whether the first type or second type is a specification
  -> SpecIndicator
  -- Flag to say whether this type is actually an effect or not
  -> Mode
  -> Checker (Bool, Substitution)

-- Base equality (helps to make things fast here)
equalTypesRelatedCoeffectsInner s rel t1 t2 _ _ _ | t1 == t2 =
  return (True, [])

equalTypesRelatedCoeffectsInner s rel fTy1@(FunTy _ grade t1 t2) fTy2@(FunTy _ grade' t1' t2') _ sp mode = do
  debugM "equalTypesRelatedCoeffectsInner (funTy left)" (pretty fTy1 <> " =? " <> pretty fTy2 <> " and " <> pretty sp)
  -- contravariant position (always approximate)
  (eq1, u1) <- equalTypesRelatedCoeffects s ApproximatedBy t1' t1 (flipIndicator sp) mode

   -- covariant position (depends: is not always over approximated)
  t2  <- substitute u1 t2
  t2' <- substitute u1 t2'
  debugM "equalTypesRelatedCoeffectsInner (funTy right)" (pretty t2 <> " == " <> pretty t2')
  (eq2, u2) <- equalTypesRelatedCoeffects s rel t2 t2' sp mode

  -- grade relation if in GradedBase
  subst <-
    if (usingExtension GradedBase) then
      case (grade, grade') of
        (Just r, Just r')  -> relGrades s r r' rel
        (Nothing, Just r') -> relGrades s (TyGrade Nothing 1) r' rel
        (Just r, Nothing)  -> relGrades s r (TyGrade Nothing 1) rel
        (Nothing, Nothing) -> return []
      else return []

  unifiers <- combineManySubstitutions s [u1, u2, subst]
  return (eq1 && eq2, unifiers)

equalTypesRelatedCoeffectsInner _ _ (TyCon con1) (TyCon con2) _ _ _
  | internalName con1 /= "Pure" && internalName con2 /= "Pure" =

    -- Some slightly ad-hoc type synonym work here:
    -- if SecurityLevels is off then Lo = Public and Hi = Private
    if not (SecurityLevels `elem` globalsExtensions ?globals)
      then if sort [internalName con1, internalName con2] == ["Lo", "Public"]
            || sort [internalName con1, internalName con2] == ["Hi", "Private"]
            then return (True, [])
            else return (con1 == con2, [])
    else
      return (con1 == con2, [])

equalTypesRelatedCoeffectsInner s rel (Diamond ef1 t1) (Diamond ef2 t2) _ sp Types = do
  debugM "equalTypesRelatedCoeffectsInner (diamond)" $ "grades " <> show ef1 <> " and " <> show ef2
  (eq, unif)   <- equalTypesRelatedCoeffects s rel t1 t2 sp Types
  (eq', unif') <- equalTypesRelatedCoeffects s rel (handledNormalise s (Diamond ef1 t1) ef1) (handledNormalise s (Diamond ef2 t2) ef2) sp Effects
  u <- combineSubstitutions s unif unif'
  return (eq && eq', u)

equalTypesRelatedCoeffectsInner s rel x@(Box c t) y@(Box c' t') k sp Types = do
  -- Debugging messages
  debugM "equalTypesRelatedCoeffectsInner (box)" $ "grades " <> show c <> " and " <> show c' <> ""

  -- Related the grades
  subst <- relGrades s c c' rel

  -- Equailty on the inner types
  (eq, subst') <- equalTypesRelatedCoeffects s rel t t' sp Types

  substU <- combineManySubstitutions s [subst, subst']
  return (eq, substU)

equalTypesRelatedCoeffectsInner s rel ty1@(TyVar var1) ty2 kind _ _ = do
  useSolver <- requiresSolver s kind
  reportM ("Equality between " <> pretty ty1 <> " and " <> pretty ty2)
  if useSolver then do
    reportM ("Is a solver variable so no substitution just an equality")
    addConstraint (rel s (TyVar var1) ty2 kind)
    return (True, [])
  else do
    -- If this isn't a solver type then use normal unfication
    subst <- unification s var1 ty2 rel
    reportM ("Not a solver therefore subst = " <> pretty subst)
    return (True, subst)

equalTypesRelatedCoeffectsInner s rel ty1 (TyVar var2) kind sp mode =
  -- Use the case above since it is symmetric
  equalTypesRelatedCoeffectsInner s rel (TyVar var2) ty1 kind sp mode

-- ## UNIQUNESS TYPES

equalTypesRelatedCoeffectsInner s rel (Star g1 t1) (Star g2 t2) _ sp mode = do
  (eq, unif)      <- equalTypesRelatedCoeffects s rel t1 t2 sp mode
  (eq', _, unif') <- equalTypes s g1 g2
  u <- combineSubstitutions s unif unif'
  return (eq && eq', u)

equalTypesRelatedCoeffectsInner s rel (Star g1 t1) t2 _ sp mode
  | t1 == t2 = throw $ UniquenessError { errLoc = s, uniquenessMismatch = NonUniqueUsedUniquely t2}
  | otherwise = do
    (g, _, u) <- equalTypes s t1 t2
    return (g, u)

equalTypesRelatedCoeffectsInner s rel t1 (Star g2 t2) k sp mode =
  equalTypesRelatedCoeffectsInner s rel (Star g2 t2) t1 k (flipIndicator sp) mode

-- ## SESSION TYPES
-- Duality is idempotent (left)
equalTypesRelatedCoeffectsInner s rel (TyApp (TyCon d') (TyApp (TyCon d) t)) t' k sp mode
  | internalName d == "Dual" && internalName d' == "Dual" =
  equalTypesRelatedCoeffectsInner s rel t t' k sp mode

-- Duality is idempotent (right)
equalTypesRelatedCoeffectsInner s rel t (TyApp (TyCon d') (TyApp (TyCon d) t')) k sp mode
  | internalName d == "Dual" && internalName d' == "Dual" =
  equalTypesRelatedCoeffectsInner s rel t t' k sp mode

-- Do duality check (left) [special case of TyApp rule]
equalTypesRelatedCoeffectsInner s rel (TyApp (TyCon d) t) t' _ sp mode
  | internalName d == "Dual" = isDualSession s rel t t' sp

equalTypesRelatedCoeffectsInner s rel t (TyApp (TyCon d) t') _ sp mode
  | internalName d == "Dual" = isDualSession s rel t t' sp

-- Do duality check (left) [special case of TyApp rule]
equalTypesRelatedCoeffectsInner s rel t0@(TyApp (TyApp (TyCon d) grd) t) t' ind sp mode
  | internalName d == "Graded" = do
    eqGradedProtocolFunction s rel grd t t' sp

equalTypesRelatedCoeffectsInner s rel t' t0@(TyApp (TyApp (TyCon d) grd) t) ind sp mode
  | internalName d == "Graded" = do
    eqGradedProtocolFunction s rel grd t t' sp

-- ## GENERAL EQUALITY

-- Equality on existential types
equalTypesRelatedCoeffectsInner s rel (TyExists x1 k1 t1) (TyExists x2 k2 t2) ind sp mode = do
  -- check kinds
  (eqK, subst1) <- equalTypesRelatedCoeffectsInner s rel k1 k2 ind sp mode
  -- replace x2 with x1 in t2
  t2' <- substitute [(x2, SubstT $ TyVar x1)] t2
  (eqT, subst2) <- equalTypesRelatedCoeffectsInner s rel t1 t2' ind sp mode

  substFinal <- combineSubstitutions s subst1 subst2
  return (eqK && eqT, substFinal)

-- Equality on type application
equalTypesRelatedCoeffectsInner s rel (TyApp t1 t2) (TyApp t1' t2') _ sp mode = do
  debugM "equalTypesRelatedCoeffectsInner (tyAp leftp)" (pretty t1 <> " = " <> pretty t1')
  (one, u1) <- equalTypesRelatedCoeffects s rel t1 t1' sp mode
  t2  <- substitute u1 t2
  t2' <- substitute u1 t2'
  debugM "equalTypesRelatedCoeffectsInner (tyApp right)" (pretty t2 <> " = " <> pretty t2')
  (two, u2) <- equalTypesRelatedCoeffects s rel t2 t2' sp mode
  unifiers <- combineSubstitutions s u1 u2
  return (one && two, unifiers)

equalTypesRelatedCoeffectsInner s rel (TyCase t1 b1) (TyCase t1' b1') k sp mode = do
  -- Check guards are equal
  (r1, u1) <- equalTypesRelatedCoeffects s rel t1 t1' sp mode
  b1  <- mapM (pairMapM (substitute u1)) b1
  b1' <- mapM (pairMapM (substitute u1)) b1'
  -- Check whether there are the same number of branches
  let r2 = (length b1) == (length b1')
  -- Sort both branches by their patterns
  let bs = zip (sortBranch b1) (sortBranch b1')
  -- For each pair of branches, check whether the patterns are equal and the results are equal
  checkBs bs (r1 && r2) u1
    where
      sortBranch :: Ord a => [(a, b)] -> [(a, b)]
      sortBranch = sortBy (\(x, _) (y, _) -> compare x y)

      pairMapM :: Monad m => (a -> m b) -> (a, a) -> m (b, b)
      pairMapM f (x, y) = do
        x' <- f x
        y' <- f y
        return (x', y')

      checkBs [] r u = return (r, u)
      checkBs (((p1, t1), (p2, t2)) : bs) r u= do
        (r1, u1) <- equalTypesRelatedCoeffects s rel p1 p2 sp mode
        t1 <- substitute u1 t1
        t2 <- substitute u1 t2
        unifiers <- combineSubstitutions s u u1
        (r2, u2) <- equalTypesRelatedCoeffects s rel t1 t2 sp mode
        unifiers <- combineSubstitutions s unifiers u2
        checkBs bs (r && r1 && r2) unifiers

-- Equality on sets in types
equalTypesRelatedCoeffectsInner s rel (TySet _ ts1) (TySet _ ts2) k sp Types =
  -- TODO: make this more powerful
  return (all (`elem` ts2) ts1 && all (`elem` ts1) ts2, [])

-- Drop through final case
equalTypesRelatedCoeffectsInner s rel t1 t2 k sp mode = do
  debugM "type Equality: Drop through case "
    ("t1 = " <> pretty t1 <> ", t2 = " <> pretty t2 <> "\n k = " <> pretty k <> "\n mode = " <> show mode)
  case mode of
    Effects -> do
      (result, putChecker) <- peekChecker (checkKind s k keffect)
      case result of
        Right res -> do
          putChecker
          eq <- effApproximates s k t1 t2
          return (eq, [])
        Left _ -> throw $ KindMismatch s Nothing keffect k

    Types ->
      case k of

        (TyCon (internalName -> "Protocol")) ->
          sessionInequality s t1 t2

        _ -> do
          handleBySolver <- requiresSolver s k
          if handleBySolver then do
            -- Go to SMT
            debugM ("equality on types of kind: " <> pretty k) (pretty t1 ++ " =? " ++ pretty t2)
            addConstraint $ Eq s t1 t2 k
            return (True, [])
          else
            -- No other way to do equality so bail
            case sp of
              FstIsSpec ->
                throw $ TypeError { errLoc = s, tyExpected = t1, tyActual = t2 }
              _ ->
                throw $ TypeError { errLoc = s, tyExpected = t1, tyActual = t2 }


-- Essentially use to report better error messages when two session type
-- are not equality
sessionInequality :: (?globals :: Globals)
    => Span -> Type -> Type -> Checker (Bool, Substitution)
sessionInequality s (TyApp (TyCon c) t) (TyApp (TyCon c') t')
  | internalName c == "Send" && internalName c' == "Send" = do
  (g, _, u) <- equalTypes s t t'
  return (g, u)

sessionInequality s (TyApp (TyCon c) t) (TyApp (TyCon c') t')
  | internalName c == "Recv" && internalName c' == "Recv" = do
  (g, _, u) <- equalTypes s t t'
  return (g, u)

sessionInequality s (TyCon c) (TyCon c')
  | internalName c == "End" && internalName c' == "End" =
  return (True, [])

sessionInequality s t1 t2 =
  throw TypeErrorAtLevel { errLoc = s, tyExpectedL = t1, tyActualL = t2 }

-- Compute the behaviour of `Graded n p` on a protocol `p`
gradedProtocolBeta :: (?globals :: Globals)
  => Type -- graded
  -> Type -- protocol/type
  -> Checker Type
gradedProtocolBeta grd protocolType@(TyApp (TyApp (TyCon c) t) s)
  | internalName c == "Send" || internalName c == "Recv" = do
    s <- gradedProtocolBeta grd s
    return $ (TyApp (TyApp (TyCon c) (Box grd t)) s)

gradedProtocolBeta grd (TyApp (TyApp (TyCon c) p1) p2)
  | internalName c == "Select" || internalName c == "Offer" = do
    p1' <- gradedProtocolBeta grd p1
    p2' <- gradedProtocolBeta grd p2
    return $ TyApp (TyApp (TyCon c) p1') p2'

gradedProtocolBeta grd protocol@(TyCon c) | internalName c == "End" = return protocol

gradedProtocolBeta grd t = return $ TyApp (TyApp (TyCon $ mkId "Graded") grd) t

-- Compute the inverse of `Graded n p` on a protocol, i.e,
-- given a protocol `p1` which we know is the result of `Graded n p` then
-- then calculate what is `p`, which will involve making some equalities between
-- grades in `p1` and `n`.
gradedProtocolBetaInvert :: (?globals :: Globals)
  => Span
  -- Explain how coeffects should be related by a solver constraint
  -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
  -> Type -- graded
  -> Type -- protocol/type
  -- Indicates whether the first type or second type is a specification
  -> SpecIndicator
  -- Flag to say whether this type is actually an effect or not
  -> Mode
  -> Checker (Type, Substitution)
-- Send/receive case
-- i.e., Graded n p = Send (Box n' t) p'
-- therefore check `n ~ n'` and then recurse
gradedProtocolBetaInvert sp rel grd protocolType@(TyApp (TyApp (TyCon c) (Box grd' t)) s) spec mode
  | internalName c == "Send" || internalName c == "Recv" = do
    -- Comput equality on grades
    (_, subst) <- equalTypesRelatedCoeffects sp rel grd grd' spec mode
    (s, subst') <- gradedProtocolBetaInvert sp rel grd s spec mode
    substFinal <- combineSubstitutions sp subst subst'
    return (TyApp (TyApp (TyCon c) t) s, substFinal)

-- Congurence on Select/Offer
gradedProtocolBetaInvert sp rel grd (TyApp (TyApp (TyCon c) p1) p2) spec mode
  | internalName c == "Select" || internalName c == "Offer" = do
    (p1', subst1) <- gradedProtocolBetaInvert sp rel grd p1 spec mode
    (p2', subst2) <- gradedProtocolBetaInvert sp rel grd p2 spec mode
    substFinal <- combineSubstitutions sp subst1 subst2
    return (TyApp (TyApp (TyCon c) p1') p2', substFinal)
--
gradedProtocolBetaInvert _ _ grd protocol@(TyCon c) _ _ | internalName c == "End" =
    return (protocol, [])

-- TODO: possibly this is the wrong fall through case?
gradedProtocolBetaInvert _ _ grd t _ _ = return (t, [])

-- Check if `Graded n p ~ p'` which may involve some normalisation in the
-- case where `p'` is a variable or some inversion in the case that `p` is a variable.
eqGradedProtocolFunction :: (?globals :: Globals)
  => Span
  -- Explain how coeffects should be related by a solver constraint
  -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
  -- These two arguments are the arguments to `Graded n p`
  -> Type -- graded
  -> Type -- protocol/type
  -- This is the argument of the type which we are trying to see if it equal to `Graded n p`
  -> Type -- compared against
  -> SpecIndicator
  -> Checker (Bool, Substitution)
eqGradedProtocolFunction sp rel grad protocolType@(TyApp (TyApp (TyCon c) t) s) (TyApp (TyApp (TyCon c') t') s') ind
  |  (internalName c == "Send" && internalName c' == "Send")
  || (internalName c == "Recv" && internalName c' == "Recv") = do
  (eq1, u1) <- equalTypesRelatedCoeffects sp rel (Box grad t) t' ind Types
  s <- substitute u1 s
  s' <- substitute u1 s'
  (eq2, u2) <- isDualSession sp rel s s' ind
  u <- combineSubstitutions sp u1 u2
  return (eq1 && eq2, u)

eqGradedProtocolFunction sp rel grad (TyApp (TyApp (TyCon c) p1) p2) (TyApp (TyApp (TyCon c') p1') p2') ind
  |  (internalName c == "Select" && internalName c' == "Select")
  || (internalName c == "Offer" && internalName c' == "Offer") = do
    -- recure duality
    (eq1, u1) <- eqGradedProtocolFunction sp rel grad p1 p1' ind
    (eq2, u2) <- eqGradedProtocolFunction sp rel grad p2 p2' ind
    u <- combineSubstitutions sp u1 u2
    return (eq1 && eq2, u)

eqGradedProtocolFunction _ _ _ (TyCon c) (TyCon c') _
  | internalName c == "End" && internalName c' == "End" =
  return (True, [])

-- try to apply `Graded` directly (beta reduce it) on `t`
eqGradedProtocolFunction sp rel grad t (TyVar v) ind = do
  t' <- gradedProtocolBeta grad t
  equalTypesRelatedCoeffects sp rel t' (TyVar v) ind Types

-- try to invert `Graded` on the protocol `t`
eqGradedProtocolFunction sp rel grad (TyVar v) t ind = do
  (t', subst) <- gradedProtocolBetaInvert sp rel grad t ind Types
  (eq, subst') <- equalTypesRelatedCoeffects sp rel t' (TyVar v) ind Types
  substFinal <- combineSubstitutions sp subst subst'
  return (eq, substFinal)

eqGradedProtocolFunction sp _ grad t1 t2 _ = throw
  TypeError{ errLoc = sp, tyExpected = (TyApp (TyApp (TyCon $ mkId "Graded") grad) t1), tyActual = t2 }

-- | Is this protocol dual to the other?
isDualSession :: (?globals :: Globals)
    => Span
       -- Explain how coeffects should be related by a solver constraint
    -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
    -> Type
    -> Type
    -- Indicates whether the first type or second type is a specification
    -> SpecIndicator
    -> Checker (Bool, Substitution)
isDualSession sp rel (TyApp (TyApp (TyCon c) t) s) (TyApp (TyApp (TyCon c') t') s') ind
  |  (internalName c == "Send" && internalName c' == "Recv")
  || (internalName c == "Recv" && internalName c' == "Send") = do
  (eq1, u1) <- equalTypesRelatedCoeffects sp rel t t' ind Types
  s <- substitute u1 s
  s' <- substitute u1 s'
  (eq2, u2) <- isDualSession sp rel s s' ind
  u <- combineSubstitutions sp u1 u2
  return (eq1 && eq2, u)

isDualSession sp rel (TyApp (TyApp (TyCon c) p1) p2) (TyApp (TyApp (TyCon c') p1') p2') ind
  |  (internalName c == "Select" && internalName c' == "Offer")
  || (internalName c == "Offer" && internalName c' == "Select") = do
    -- recure duality
    (eq1, u1) <- isDualSession sp rel p1 p1' ind
    (eq2, u2) <- isDualSession sp rel p2 p2' ind
    u <- combineSubstitutions sp u1 u2
    return (eq1 && eq2, u)


isDualSession _ _ (TyCon c) (TyCon c') _
  | internalName c == "End" && internalName c' == "End" =
  return (True, [])

isDualSession sp rel t (TyVar v) ind =
  equalTypesRelatedCoeffects sp rel (TyApp (TyCon $ mkId "Dual") t) (TyVar v) ind Types

isDualSession sp rel (TyVar v) t ind =
  equalTypesRelatedCoeffects sp rel (TyVar v) (TyApp (TyCon $ mkId "Dual") t) ind Types

isDualSession sp _ t1 t2 _ = throw
  SessionDualityError{ errLoc = sp, errTy1 = t1, errTy2 = t2 }

-- | Check if two effect terms have the same effect type
twoEqualEffectTypes :: (?globals :: Globals) => Span -> Type -> Type -> Checker (Type, Substitution)
twoEqualEffectTypes s ef1 ef2 = do
    mefTy1 <- isEffectType s ef1
    mefTy2 <- isEffectType s ef2
    case mefTy1 of
      Right efTy1 ->
        case mefTy2 of
          Right efTy2 -> do
            -- Check that the types of the effect terms match
            (eq, _, u) <- equalTypes s efTy1 efTy2
            if eq then do
              return (efTy1, u)
            else throw $ KindMismatch { errLoc = s, tyActualK = Just ef1, kExpected = efTy1, kActual = efTy2 }
          Left k -> throw $ UnknownResourceAlgebra { errLoc = s, errTy = ef2 , errK = k }
      Left k -> throw $ UnknownResourceAlgebra { errLoc = s, errTy = ef1 , errK = k }

-- | Find out if a type is indexed overall (i.e., is a GADT)
isIndexedType :: Type -> Checker Bool
isIndexedType t = do
  b <- typeFoldM TypeFold
      { tfTy = \_ -> return $ Const False
      , tfFunTy = \_ _ (Const x) (Const y) -> return $ Const (x || y)
      , tfTyCon = \c -> do {
          st <- get;
          return $ Const $ case lookup c (typeConstructors st) of Just (_, _, indices) -> indices /= []; Nothing -> False }
      , tfBox = \_ (Const x) -> return $ Const x
      , tfDiamond = \_ (Const x) -> return $ Const x
      , tfStar = \_ (Const x) -> return $ Const x
      , tfTyVar = \_ -> return $ Const False
      , tfTyApp = \(Const x) (Const y) -> return $ Const (x || y)
      , tfTyInt = \_ -> return $ Const False
      , tfTyRational = \_ -> return $ Const False
      , tfTyGrade = \_ _ -> return $ Const False
      , tfTyInfix = \_ (Const x) (Const y) -> return $ Const (x || y)
      , tfSet = \_ _ -> return $ Const False
      , tfTyCase = \_ _ -> return $ Const False
      , tfTySig = \(Const b) _ _ -> return $ Const b
      , tfTyExists = \_ _ (Const a) -> return $ Const a } t
  return $ getConst b

-- Given a type term, works out if its kind is actually an effect type
-- if so, returns `Right effTy` where `effTy` is the effect type
-- otherwise, returns `Left k` where `k` is the kind of the original type term
isEffectType :: (?globals :: Globals) => Span -> Type -> Checker (Either Kind Type)
isEffectType s ty = do
  (effTy, _, _) <- synthKind s ty
  (result, putChecker) <- peekChecker (checkKind s effTy keffect)
  case result of
    Right res -> do
      putChecker
      return $ Right effTy
    Left err -> return $ Left effTy

-- `refineBinderQuantification ctxt ty`
-- Given a list of variable-kind information `ctxt` binding over a type `ty`
-- then calculate based on the usage of the type variables whether they are
-- truly universal quantifiers, or whether some are actually pi-types.
refineBinderQuantification :: (?globals :: Globals) => Ctxt Kind -> Type -> Checker (Ctxt (Kind, Quantifier))
refineBinderQuantification ctxt ty = mapM computeQuantifier ctxt
  where
    computeQuantifier (id, kind) = do
      result <- aux id ty
      return $ if result then (id, (kind, BoundQ)) else (id, (kind, ForallQ))

    aux :: Id -> Type -> Checker Bool
    aux id (FunTy _ (Just g) t1 t2) = liftM2 (||) (liftM2 (||) (aux id t1) (aux id t2)) (aux id g)
    aux id (FunTy _ Nothing t1 t2)  = liftM2 (||) (aux id t1) (aux id t2)
    aux id (Box _ t)       = aux id t
    aux id (Diamond _ t)   = aux id t
    aux id (Star _ t)      = aux id t
    aux id t@(TyApp _ _)   =
      case leftmostOfApplication t of
        TyCon tyConId -> do
          st <- get
          case lookup tyConId (typeConstructors st) of
            Just (_, _, indices) -> do
              -- For this type constructor `tyConId`
              -- if any of its argument positions `i` is an index
              -- then check if the `id` here is in the term for that argument
              return $ any (\i ->
                 if i < length (typeArguments t)
                  then id `elem` freeVars (typeArguments t !! i)
                  else False) indices
            Nothing -> throw UnboundVariableError { errLoc = nullSpan , errId = id }
        -- unusual- put possible (e.g., `f t`) give up and go for ForallQ
        _ -> return False
    aux id (TyInfix _ t1 t2) = liftM2 (||) (aux id t1) (aux id t2)
    aux id (TySig t k)       = liftM2 (||) (aux id t) (aux id k)
    aux id (TyCase t ts)     = liftM2 (||) (aux id t) (anyM (\(_, t) -> aux id t) ts)
      where
        anyM f xs = mapM f xs >>= (return . or)
    aux id _ = return False