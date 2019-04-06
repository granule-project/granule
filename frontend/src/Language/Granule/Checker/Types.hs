{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

{-# options_ghc -fno-warn-missing-signatures #-}

module Language.Granule.Checker.Types
    (
    -- ** Equality proofs
      equalityProofSubstitution
    , equalityProofConstraints

    -- ** Specification indicators
    , SpecIndicator(..)

    -- ** Equality tests
    , checkEquality

    , requireEqualTypes
    , requireEqualTypesRelatedCoeffects

    , typesAreEqual
    , typesAreEqualWithCheck
    , lTypesAreEqual

    , equalTypesRelatedCoeffects

    , equalTypes
    , lEqualTypes

    , equalTypesWithPolarity
    , lEqualTypesWithPolarity

    , equalTypesWithUniversalSpecialisation

    , joinTypes

    -- *** Instance Equality
    , equalInstances
    , instancesAreEqual

    -- *** Kind Equality
    , equalKinds
    ) where

import Control.Monad.State.Strict
import Data.List

import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Instance
import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.Variables

import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Utils


------------------------------
----- Inequality Reasons -----
------------------------------

type InequalityReason = CheckerError


equalityErr :: (Monad m) => InequalityReason -> m EqualityResult
equalityErr = pure . Left


effectMismatch s ef1 ef2 = equalityErr $
  EffectMismatch{ errLoc = s, effExpected = ef1, effActual = ef2 }


coeffectMismatch s c1 c2 = equalityErr $
  CoeffectEqualityMismatch{ errLoc = s, errDesc = "", errC1 = c1, errC2 = c2 }


unequalSessionTypes s t1 t2 = equalityErr $
  TypeError{ errLoc = s, tyExpected = t1, tyActual = t2 }


sessionsNotDual s t1 t2 = equalityErr $
  SessionDualityError{ errLoc = s, errTy1 = t1, errTy2 = t2 }


kindEqualityIsUndefined s k1 k2 t1 t2 = equalityErr $
  UndefinedEqualityKindError{ errLoc = s, errTy1 = t1
                            , errK1 = k1, errTy2 = t2, errK2 = k2 }


contextDoesNotAllowUnification s x y = equalityErr $
  UnificationDisallowed { errLoc = s, errTy1 = x, errTy2 = y }


cannotUnifyUniversalWithConcrete s n kind t = equalityErr $
  UnificationFail{ errLoc = s, errVar = n, errKind = kind, errTy = t }


twoUniversallyQuantifiedVariablesAreUnequal s v1 v2 = equalityErr $
  CannotUnifyUniversalWithConcrete{ errLoc = s, errVar1 = v1, errVar2 = v2 }


nonUnifiable s t1 t2 = equalityErr $
  UnificationError{ errLoc = s, errTy1 = t1, errTy2 = t2}


-- | Generic inequality for when a more specific reason is not known.
unequalNotSpecified s v1 v2 = equalityErr $
  EqualityMismatch{ errLoc = s, errDesc = "", errVar1 = v1, errVar2 = v2 }


-- | Generic (kind) inequality for when a more specific reason is not known.
unequalKinds s k1 k2 = equalityErr $
  KindEqualityMismatch{ errLoc = s, errDesc = "", errK1 = k1, errK2 = k2 }


cannotBeBoth s v s1 s2 = equalityErr $
  CannotBeBoth{ errLoc = s, errVar = v, errVal1 = s1, errVal2 = s2 }


-- | Attempt to unify a non-type variable with a type.
illKindedUnifyVar sp (v, k1) (t, k2) = equalityErr $
   UnificationKindError{ errLoc = sp, errTy1 = TyVar v
                       , errK1 = k1, errTy2 = t, errK2 = k2 }


-- | Test @x@ and @y@ for boolean equality. If they are
-- | equal then return a trivial proof of equality, otherwise
-- | use @desc@ to provide a descriptive reason for inequality.
directEqualityTest desc s x y =
  if x == y then trivialEquality else equalityErr $
  EqualityMismatch{ errLoc = s, errDesc = desc, errVar1 = x, errVar2 = y }


miscErr :: CheckerError -> Checker EqualityResult
miscErr = equalityErr


-- | Infer a kind for the given type (promoting any errors to the inequality reason),
-- | and run the prover on the kind.
withInferredKind :: (?globals :: Globals) => Span -> Type
                 -> (Kind -> Checker EqualityResult)
                 -> Checker EqualityResult
withInferredKind sp t c =
  inferKindOfTypeSafe sp t >>= either miscErr c


-- | Execute the prover with the most general unifier of
-- | the two coeffects as an argument.
withMguCoeffectTypes :: (?globals :: Globals) => Span -> Coeffect -> Coeffect
                     -> (Type -> Checker EqualityResult)
                     -> Checker EqualityResult
withMguCoeffectTypes sp c c' pf =
  mguCoeffectTypesSafe sp c c' >>= either miscErr pf


--------------------------
----- Equality types -----
--------------------------


-- | A proof of equality.
type EqualityProof = ([Constraint], Substitution)


-- | Get the substitution from a proof of equality.
equalityProofSubstitution :: EqualityProof -> Substitution
equalityProofSubstitution = snd


-- | Get the constraints from a proof of equality.
equalityProofConstraints :: EqualityProof -> [Constraint]
equalityProofConstraints = fst


type EqualityResult = Either InequalityReason EqualityProof


-- | True if the check for equality was successful.
equalityResultIsSuccess :: EqualityResult -> Bool
equalityResultIsSuccess = either (const False) (const True)


-- | A proof of a trivial equality ('x' and 'y' are equal because we say so).
trivialEquality' :: EqualityResult
trivialEquality' = pure ([], [])


-- | Equality where nothing needs to be done.
trivialEquality :: Checker EqualityResult
trivialEquality = pure trivialEquality'


-- | Attempt to prove equality using the result of a previous proof.
eqSubproof :: (Monad m) => EqualityResult -> (EqualityProof -> m (Either InequalityReason a)) -> m (Either InequalityReason a)
eqSubproof e f = either (pure . Left) f e


-- | Require that two proofs of equality hold, and if so, combine them.
combinedEqualities :: (?globals :: Globals) => Span -> EqualityResult -> EqualityResult -> Checker EqualityResult
combinedEqualities s e1 e2 =
  eqSubproof e1 $ \eq1res -> do
    eqSubproof e2 $ \eq2res -> do
      let u1 = equalityProofSubstitution eq1res
          u2 = equalityProofSubstitution eq2res
          cs = equalityProofConstraints eq1res
               <> equalityProofConstraints eq2res
      uf <- combineSubstitutionsSafe s u1 u2
      case uf of
        Left (v, s1, s2) -> cannotBeBoth s v s1 s2
        Right cuf -> pure . pure $ (cs, cuf)


-- | An equality under the given proof.
equalWith :: EqualityProof -> EqualityResult
equalWith = Right


-- | Update the state with information from the equality proof.
enactEquality :: (?globals :: Globals) => Type -> EqualityProof -> Checker ()
enactEquality t eqres = do
  let u = equalityProofSubstitution eqres
      cs = equalityProofConstraints eqres
  _ <- substitute u t
  mapM_ addConstraint cs


-- | Check for equality, and update the checker state.
checkEquality :: (?globals :: Globals)
  => (Type -> Checker EqualityResult) -> Type -> Checker EqualityResult
checkEquality eqm t = do
  eq <- eqm t
  case eq of
    Right eqres -> enactEquality t eqres
    Left _ -> pure ()
  pure eq


-- | Require that an equality holds, and perform a unification
-- | to reflect this equality in the checker.
requireEqualityResult :: (?globals :: Globals)
  => Type -> Checker EqualityResult -> Checker EqualityProof
requireEqualityResult t = (>>= either throw (\r -> enactEquality t r >> pure r))


------------------
-- Type helpers --
------------------


-- | Explains how coeffects should be related by a solver constraint.
type Rel = (Span -> Coeffect -> Coeffect -> Type -> Constraint)


type EqualityProver a b = (?globals :: Globals) =>
  Span -> Rel -> SpecIndicator -> a -> a -> Checker b


type EqualityProver' a b = (?globals :: Globals) =>
  Span -> a -> a -> Checker b


type EqualityProverWithSpec a b = (?globals :: Globals) =>
  Span -> SpecIndicator -> a -> a -> Checker b


---------------------------------
----- Bulk of equality code -----
---------------------------------


-- | True if the two types are equal.
typesAreEqual :: EqualityProver' Type Bool
typesAreEqual s t1 t2 =
  fmap equalityResultIsSuccess $ equalTypes s t1 t2


-- | True if the two types are equal.
typesAreEqualWithCheck :: EqualityProver' Type Bool
typesAreEqualWithCheck s t1 t2 =
  fmap equalityResultIsSuccess $ checkEquality (equalTypes s t1) t2


lTypesAreEqual :: EqualityProver' Type Bool
lTypesAreEqual s t1 t2 = fmap (either (const False) (const True)) $ lEqualTypes s t1 t2


requireEqualTypes :: EqualityProver' Type EqualityProof
requireEqualTypes s t1 t2 =
    requireEqualityResult t2 $ equalTypes s t1 t2


requireEqualTypesRelatedCoeffects :: EqualityProver Type EqualityProof
requireEqualTypesRelatedCoeffects s rel spec t1 t2 =
    requireEqualityResult t2 $ equalTypesRelatedCoeffects s rel spec t1 t2


lEqualTypesWithPolarity :: EqualityProverWithSpec Type EqualityResult
lEqualTypesWithPolarity s pol = equalTypesRelatedCoeffects s ApproximatedBy pol


equalTypesWithPolarity :: EqualityProverWithSpec Type EqualityResult
equalTypesWithPolarity s pol = equalTypesRelatedCoeffects s Eq pol


lEqualTypes :: EqualityProver' Type EqualityResult
lEqualTypes s = equalTypesRelatedCoeffects s ApproximatedBy SndIsSpec


equalTypes :: EqualityProver' Type EqualityResult
equalTypes s = equalTypesRelatedCoeffects s Eq SndIsSpec


equalTypesWithUniversalSpecialisation :: EqualityProver' Type EqualityResult
equalTypesWithUniversalSpecialisation s =
  equalTypesRelatedCoeffects s Eq SndIsSpec


-- | Indicates whether the first type or second type is a specification.
data SpecIndicator = FstIsSpec | SndIsSpec | PatternCtxt
  deriving (Eq, Show)


flipIndicator :: SpecIndicator -> SpecIndicator
flipIndicator FstIsSpec = SndIsSpec
flipIndicator SndIsSpec = FstIsSpec
flipIndicator PatternCtxt = PatternCtxt

{- | Check whether two types are equal, and at the same time
     generate coeffect equality constraints and a unifier
      Polarity indicates which -}
equalTypesRelatedCoeffects :: EqualityProver Type EqualityResult
equalTypesRelatedCoeffects s rel sp (FunTy t1 t2) (FunTy t1' t2') = do
  -- contravariant position (always approximate)
  eq1 <- equalTypesRelatedCoeffects s ApproximatedBy (flipIndicator sp) t1' t1
  eq2 <- eqSubproof eq1 $ \eqres -> do
           let u1 = equalityProofSubstitution eqres
           -- covariant position (depends: is not always over approximated)
           t2 <- substitute u1 t2
           t2' <- substitute u1 t2'
           equalTypesRelatedCoeffects s rel sp t2 t2'
  combinedEqualities s eq1 eq2

equalTypesRelatedCoeffects s _ _ (TyCon con1) (TyCon con2) =
  directEqualityTest "Type constructors" s con1 con2

-- THE FOLLOWING FOUR CASES ARE TEMPORARY UNTIL WE MAKE 'Effect' RICHER

-- Over approximation by 'IO' "monad"
equalTypesRelatedCoeffects s rel sp (Diamond ef t1) (Diamond ["IO"] t2)
    = equalTypesRelatedCoeffects s rel sp t1 t2

-- Under approximation by 'IO' "monad"
equalTypesRelatedCoeffects s rel sp (Diamond ["IO"] t1) (Diamond ef t2)
    = equalTypesRelatedCoeffects s rel sp t1 t2

-- Over approximation by 'Session' "monad"
equalTypesRelatedCoeffects s rel sp (Diamond ef t1) (Diamond ["Session"] t2)
    | "Com" `elem` ef || null ef
      = equalTypesRelatedCoeffects s rel sp t1 t2

-- Under approximation by 'Session' "monad"
equalTypesRelatedCoeffects s rel sp (Diamond ["Session"] t1) (Diamond ef t2)
    | "Com" `elem` ef || null ef
      = equalTypesRelatedCoeffects s rel sp t1 t2

equalTypesRelatedCoeffects s rel sp (Diamond ef1 t1) (Diamond ef2 t2) = do
  if ( ef1 == ef2
     -- Effect approximation
     || ef1 `isPrefixOf` ef2
     -- Communication effect analysis is idempotent
     || (nub ef1 == ["Com"] && nub ef2 == ["Com"]))
  then equalTypesRelatedCoeffects s rel sp t1 t2
  else effectMismatch s ef1 ef2

equalTypesRelatedCoeffects s rel sp x@(Box c t) y@(Box c' t') = do
  -- Debugging messages
  debugM "equalTypesRelatedCoeffects (pretty)" $ pretty c <> " == " <> pretty c'
  debugM "equalTypesRelatedCoeffects (show)" $ "[ " <> show c <> " , " <> show c' <> "]"
  eq1 <- equalCoeffects s rel sp (x, c) (y, c')
  eq2 <- equalTypesRelatedCoeffects s rel sp t t'
  combinedEqualities s eq1 eq2

equalTypesRelatedCoeffects s rel sp t1@(TyCoeffect c1) t2@(TyCoeffect c2) =
  equalCoeffects s rel sp (t1, c1) (t2, c2)

equalTypesRelatedCoeffects s _ _ (TyVar n) (TyVar m) | n == m = do
  checkerState <- get
  case lookup n (tyVarContext checkerState) of
    Just _ -> trivialEquality
    Nothing -> miscErr $ UnboundTypeVariable{ errLoc = s, errId = n }

equalTypesRelatedCoeffects s _ sp (TyVar n) (TyVar m) = do
  checkerState <- get
  debugM "variable equality" $ pretty n <> " ~ " <> pretty m <> " where "
                            <> pretty (lookup n (tyVarContext checkerState)) <> " and "
                            <> pretty (lookup m (tyVarContext checkerState))

  case (lookup n (tyVarContext checkerState), lookup m (tyVarContext checkerState)) of

    (Just (_, ForallQ), Just (_, ForallQ)) ->
        twoUniversallyQuantifiedVariablesAreUnequal s n m

    -- We can unify a universal a dependently bound universal
    (Just (k1, ForallQ), Just (k2, BoundQ)) ->
      tyVarConstraint (k1, n) (k2, m)

    (Just (k1, BoundQ), Just (k2, ForallQ)) ->
      tyVarConstraint (k1, n) (k2, m)


    -- We can unify two instance type variables
    (Just (k1, InstanceQ), Just (k2, BoundQ)) ->
        tyVarConstraint (k1, n) (k2, m)

    -- We can unify two instance type variables
    (Just (k1, BoundQ), Just (k2, InstanceQ)) ->
        tyVarConstraint (k1, n) (k2, m)

    -- We can unify two instance type variables
    (Just (k1, InstanceQ), Just (k2, InstanceQ)) ->
        tyVarConstraint (k1, n) (k2, m)

    -- We can unify two instance type variables
    (Just (k1, BoundQ), Just (k2, BoundQ)) ->
        tyVarConstraint (k1, n) (k2, m)

    -- But we can unify a forall and an instance
    (Just (k1, InstanceQ), Just (k2, ForallQ)) ->
        tyVarConstraint (k1, n) (k2, m)

    -- But we can unify a forall and an instance
    (Just (k1, ForallQ), Just (k2, InstanceQ)) ->
        tyVarConstraint (k1, n) (k2, m)

    (t1, t2) -> error $ pretty s <> "-" <> show sp <> "\n"
              <> pretty n <> " : " <> show t1
              <> "\n" <> pretty m <> " : " <> show t2
  where
    tyVarConstraint (k1, n) (k2, m) = do
      case k1 `joinKind` k2 of
        Just (KPromote (TyCon kc)) -> do

          withInferredKind s (TyCon kc) $ \k -> do
            -- Create solver vars for coeffects
            let constrs = case k of
                            KCoeffect -> [Eq s (CVar n) (CVar m) (TyCon kc)]
                            _ -> []
            pure $ equalWith (constrs, [(m, SubstT $ TyVar n)])
        Just _ ->
          pure $ equalWith ([], [(m, SubstT $ TyVar n)])
        Nothing -> unequalNotSpecified s n m


-- Duality is idempotent (left)
equalTypesRelatedCoeffects s rel sp (TyApp (TyCon d') (TyApp (TyCon d) t)) t'
  | internalName d == "Dual" && internalName d' == "Dual" =
  equalTypesRelatedCoeffects s rel sp t t'

-- Duality is idempotent (right)
equalTypesRelatedCoeffects s rel sp t (TyApp (TyCon d') (TyApp (TyCon d) t'))
  | internalName d == "Dual" && internalName d' == "Dual" =
  equalTypesRelatedCoeffects s rel sp t t'

equalTypesRelatedCoeffects s rel sp (TyVar n) t = do
  checkerState <- get
  debugM "Types.equalTypesRelatedCoeffects on TyVar"
          $ "span: " <> show s
          <> "\nTyVar: " <> show n <> " with " <> show (lookup n (tyVarContext checkerState))
          <> "\ntype: " <> show t <> "\nspec indicator: " <> show sp

  k2 <- inferKindOfType s t

  -- Do an occurs check for types
  case k2 of
    KType ->
       if n `elem` freeVars t
         then throw OccursCheckFail { errLoc = s, errVar = n, errTy = t }
         else return ()
    _ -> return ()

  case lookup n (tyVarContext checkerState) of
    -- We can unify an instance with a concrete type
    (Just (k1, q)) | (q == BoundQ) || (q == InstanceQ && sp /= PatternCtxt) -> do
      withInferredKind s t $ \k2 ->
        case k1 `joinKind` k2 of
          Nothing -> illKindedUnifyVar s (n, k1) (t, k2)

          -- If the kind is Nat, then create a solver constraint
          Just (KPromote (TyCon (internalName -> "Nat"))) -> do
            nat <- compileNatKindedTypeToCoeffect s t
            pure $ equalWith ([Eq s (CVar n) nat (TyCon $ mkId "Nat")], [(n, SubstT t)])

          Just _ -> pure $ equalWith ([], [(n, SubstT t)])

    -- NEW

    (Just (k1, ForallQ)) -> do
       -- Infer the kind of this equality
       withInferredKind s t $ \k2 -> do
         let kind = k1 `joinKind` k2

         -- If the kind if nat then set up and equation as there might be a
         -- pausible equation involving the quantified variable
         case kind of
           Just (KPromote (TyCon (Id "Nat" "Nat"))) -> do
             c1 <- compileNatKindedTypeToCoeffect s (TyVar n)
             c2 <- compileNatKindedTypeToCoeffect s t
             pure $ equalWith ([Eq s c1 c2 (TyCon $ mkId "Nat")], [(n, SubstT t)])
           Nothing -> illKindedUnifyVar s (n, k1) (t, k2)
           Just kind -> cannotUnifyUniversalWithConcrete s n kind t

    (Just (_, InstanceQ)) -> error "Please open an issue at https://github.com/dorchard/granule/issues"
    (Just (_, BoundQ)) -> error "Please open an issue at https://github.com/dorchard/granule/issues"
    Nothing -> miscErr $ UnboundVariableError{ errLoc = s, errId = n }


equalTypesRelatedCoeffects s rel sp t (TyVar n) =
  equalTypesRelatedCoeffects s rel (flipIndicator sp) (TyVar n) t

-- Do duality check (left) [special case of TyApp rule]
equalTypesRelatedCoeffects s rel sp (TyApp (TyCon d) t) t'
  | internalName d == "Dual" = isDualSession s rel sp t t'

equalTypesRelatedCoeffects s rel sp t (TyApp (TyCon d) t')
  | internalName d == "Dual" = isDualSession s rel sp t t'

-- Equality on type application
equalTypesRelatedCoeffects s rel sp (TyApp t1 t2) (TyApp t1' t2') = do
  eq1 <- equalTypesRelatedCoeffects s rel sp t1 t1'
  eq2 <- eqSubproof eq1 (\eqres -> do
           let u1 = equalityProofSubstitution eqres
           t2 <- substitute u1 t2
           t2' <- substitute u1 t2'
           equalTypesRelatedCoeffects s rel sp t2 t2')
  combinedEqualities s eq1 eq2


equalTypesRelatedCoeffects s rel _ t1 t2 = do
  debugM "equalTypesRelatedCoeffects" $ "called on: " <> show t1 <> "\nand:\n" <> show t2
  equalOtherKindedTypesGeneric s t1 t2

{- | Equality on other types (e.g. Nat and Session members) -}
equalOtherKindedTypesGeneric :: (?globals :: Globals)
    => Span
    -> Type
    -> Type
    -> Checker EqualityResult
equalOtherKindedTypesGeneric s t1 t2 = do
  withInferredKind s t1 $ \k1 -> withInferredKind s t2 $ \k2 ->
    if k1 == k2 then
      case k1 of
        KPromote (TyCon (internalName -> "Nat")) -> do
          c1 <- compileNatKindedTypeToCoeffect s t1
          c2 <- compileNatKindedTypeToCoeffect s t2
          pure $ equalWith ([Eq s c1 c2 (TyCon $ mkId "Nat")], [])

        KPromote (TyCon (internalName -> "Protocol")) ->
          sessionInequality s t1 t2

        KType -> nonUnifiable s t1 t2

        _ -> kindEqualityIsUndefined s k1 k2 t1 t2
    else nonUnifiable s t1 t2

-- Essentially use to report better error messages when two session type
-- are not equality
sessionInequality :: (?globals :: Globals)
    => Span -> Type -> Type -> Checker EqualityResult
sessionInequality s (TyApp (TyCon c) t) (TyApp (TyCon c') t')
  | internalName c == "Send" && internalName c' == "Send" = do
  equalTypes s t t'

sessionInequality s (TyApp (TyCon c) t) (TyApp (TyCon c') t')
  | internalName c == "Recv" && internalName c' == "Recv" = do
  equalTypes s t t'

sessionInequality s (TyCon c) (TyCon c')
  | internalName c == "End" && internalName c' == "End" =
  trivialEquality

sessionInequality s t1 t2 = unequalSessionTypes s t1 t2

isDualSession :: (?globals :: Globals)
    => Span
       -- Explain how coeffects should be related by a solver constraint
    -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
    -- Indicates whether the first type or second type is a specification
    -> SpecIndicator
    -> Type
    -> Type
    -> Checker EqualityResult
isDualSession sp rel ind (TyApp (TyApp (TyCon c) t) s) (TyApp (TyApp (TyCon c') t') s')
  |  (internalName c == "Send" && internalName c' == "Recv")
  || (internalName c == "Recv" && internalName c' == "Send") = do
  eq1 <- equalTypesRelatedCoeffects sp rel ind t t'
  eq2 <- isDualSession sp rel ind s s'
  combinedEqualities sp eq1 eq2

isDualSession _ _ _ (TyCon c) (TyCon c')
  | internalName c == "End" && internalName c' == "End" =
  trivialEquality

isDualSession sp rel ind t (TyVar v) =
  equalTypesRelatedCoeffects sp rel ind (TyApp (TyCon $ mkId "Dual") t) (TyVar v)

isDualSession sp rel ind (TyVar v) t =
  equalTypesRelatedCoeffects sp rel ind (TyVar v) (TyApp (TyCon $ mkId "Dual") t)

isDualSession sp _ _ t1 t2 = sessionsNotDual sp t1 t2


-- Essentially equality on types but join on any coeffects
joinTypes :: (?globals :: Globals) => Span -> Type -> Type -> Checker Type
joinTypes s t t' | t == t' = return t

joinTypes s (FunTy t1 t2) (FunTy t1' t2') = do
  t1j <- joinTypes s t1' t1 -- contravariance
  t2j <- joinTypes s t2 t2'
  return (FunTy t1j t2j)

joinTypes _ (TyCon t) (TyCon t') | t == t' = return (TyCon t)

joinTypes s (Diamond ef t) (Diamond ef' t') = do
  tj <- joinTypes s t t'
  if ef `isPrefixOf` ef'
    then return (Diamond ef' tj)
    else
      if ef' `isPrefixOf` ef
      then return (Diamond ef tj)
      else effectMismatch s ef ef' >>= either throw (pure . const t')

joinTypes s (Box c t) (Box c' t') = do
  coeffTy <- mguCoeffectTypes s c c'
  -- Create a fresh coeffect variable
  topVar <- freshTyVarInContext (mkId "") (promoteTypeToKind coeffTy)
  -- Unify the two coeffects into one
  addConstraint (ApproximatedBy s c  (CVar topVar) coeffTy)
  addConstraint (ApproximatedBy s c' (CVar topVar) coeffTy)
  tUpper <- joinTypes s t t'
  return $ Box (CVar topVar) tUpper

joinTypes s (TyInt n) (TyVar m) = do
  -- Create a fresh coeffect variable
  let ty = TyCon $ mkId "Nat"
  var <- freshTyVarInContext m (KPromote ty)
  -- Unify the two coeffects into one
  addConstraint (Eq s (CNat n) (CVar var) ty)
  return $ TyInt n

joinTypes s (TyVar n) (TyInt m) = joinTypes s (TyInt m) (TyVar n)

joinTypes s (TyVar n) (TyVar m) = do
  -- Create fresh variables for the two tyint variables
  -- TODO: how do we know they are tyints? Looks suspicious
  --let kind = TyCon $ mkId "Nat"
  --nvar <- freshTyVarInContext n kind
  --mvar <- freshTyVarInContext m kind
  -- Unify the two variables into one
  --addConstraint (ApproximatedBy s (CVar nvar) (CVar mvar) kind)
  --return $ TyVar n
  -- TODO: FIX. The above can't be right.
  error $ "Trying to join two type variables: " ++ pretty n ++ " and " ++ pretty m

joinTypes s (TyApp t1 t2) (TyApp t1' t2') = do
  t1'' <- joinTypes s t1 t1'
  t2'' <- joinTypes s t2 t2'
  return (TyApp t1'' t2'')

-- TODO: Create proper substitutions
joinTypes s (TyVar _) t = return t
joinTypes s t (TyVar _) = return t

joinTypes s t1 t2 = throw
  NoUpperBoundError{ errLoc = s, errTy1 = t1, errTy2 = t2 }


----------------------------
----- Instance Helpers -----
----------------------------


-- | Prove or disprove the equality of two instances in the current context.
equalInstances :: (?globals :: Globals) => Span -> Inst -> Inst -> Checker EqualityResult
equalInstances sp instx insty =
  let ts1 = instParams instx
      ts2 = instParams insty
  in foldM (\eq (t1,t2) -> equalTypes sp t1 t2 >>= combinedEqualities sp eq) trivialEquality' (zip ts1 ts2)


-- TODO: update this (instancesAreEqual) to use 'solveConstraintsSafe' to
-- determine if two instances are equal after solving.
-- "instancesAreEqual'" (in Checker) should then be removed
--      - GuiltyDolphin (2019-03-17)

-- | True if the two instances can be proven to be equal in the current context.
instancesAreEqual :: (?globals :: Globals) => Span -> Inst -> Inst -> Checker Bool
instancesAreEqual s t1 t2 = fmap equalityResultIsSuccess $ equalInstances s t1 t2


-----------------------
-- Coeffect equality --
-----------------------


equalCoeffects :: EqualityProver (Type, Coeffect) EqualityResult
equalCoeffects s rel sp (t1, c1) (t2, c2) = do
  withMguCoeffectTypes s c1 c2 $ \kind -> do
    case sp of
      SndIsSpec -> do
        pure $ equalWith ([rel s c1 c2 kind], [])
      FstIsSpec -> do
        pure $ equalWith ([rel s c2 c1 kind], [])
      _ -> contextDoesNotAllowUnification s t1 t2


-------------------
-- Kind equality --
-------------------


-- | Determine whether two kinds are equal, and under what proof.
-- |
-- | This is presently rather simplistic, and allows poly-kinds to
-- | unify with anything.
equalKinds :: (?globals :: Globals) => Span -> Kind -> Kind -> Checker EqualityResult
equalKinds _ k1 k2 | k1 == k2 = trivialEquality
equalKinds _ (KVar v) k = pure $ equalWith ([], [(v, SubstK k)])
equalKinds _ k (KVar v) = pure $ equalWith ([], [(v, SubstK k)])
equalKinds _ KType KType = trivialEquality
equalKinds sp (KFun k1 k1Arg) (KFun k2 k2Arg) = do
  pf1 <- equalKinds sp k1 k2
  pf2 <- equalKinds sp k1Arg k2Arg
  combinedEqualities sp pf1 pf2
equalKinds sp k1 k2 = unequalKinds sp k1 k2
