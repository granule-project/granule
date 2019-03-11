{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Types where

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Data.List

import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Errors
import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.Variables

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Utils


------------------------------
----- Inequality Reasons -----
------------------------------


type InequalityReason = CheckerError


equalityErr :: (?globals :: Globals, Monad m) => InequalityReason -> m EqualityResult
equalityErr = pure . Left


effectMismatch s ef1 ef2 = equalityErr $
  GradingError (Just s) $
    concat ["Effect mismatch: ", prettyQuoted ef1, " not equal to ", prettyQuoted ef2]


unequalSessionTypes s t1 t2 = equalityErr $
  GenericError (Just s) $
    concat ["Session type ", prettyQuoted t1, " is not equal to ", prettyQuoted t2]


sessionsNotDual s t1 t2 = equalityErr $
  GenericError (Just s) $
    concat ["Session type ", prettyQuoted t1, " is not dual to ", prettyQuoted t2]


kindEqualityIsUndefined s k1 k2 t1 t2 = equalityErr $
  KindError (Just s) $
    concat [ "Equality is not defined between kinds "
           , pretty k1, " and ", pretty k2
           , "\t\n from equality "
           , prettyQuoted t2, " and ", prettyQuoted t1 <> " equal."]


contextDoesNotAllowUnification s x y = equalityErr $
  GenericError (Just s) $
    concat [ "Trying to unify ", prettyQuoted x, " and ", prettyQuoted y
           , " but in a context where unification is not allowed."]


cannotUnifyUniversalWithConcrete s n kind t = equalityErr $
  GenericError (Just s) $
    concat [ "Cannot unify a universally quantified type variable "
           , prettyQuoted (TyVar n), " of kind ", prettyQuoted kind
           , " with a concrete type " <> prettyQuoted t]


twoUniversallyQuantifiedVariablesAreUnequal s v1 v2 = equalityErr $
  GenericError (Just s) $
    concat [ quoteTyVar v1, " and ", quoteTyVar v2
           , " are both universally quantified, and thus cannot be equal."]
  where quoteTyVar = prettyQuoted . TyVar


-- | Generic inequality for when a more specific reason is not known.
unequalNotSpecified s v1 v2 = equalityErr $
  GenericError (Just s) $
    concat [ quoteTyVar v1, " and ", quoteTyVar v2
           , " are not equal."]
  where quoteTyVar = prettyQuoted . TyVar


-- | Test @x@ and @y@ for boolean equality. If they are
-- | equal then return a trivial proof of equality, otherwise
-- | use @desc@ to provide a descriptive reason for inequality.
directEqualityTest desc s x y =
  if x == y then trivialEquality else equalityErr $
  GenericError (Just s) $
    concat [desc, " ", prettyQuoted x, " and ", prettyQuoted y
           , " are not equal."]


miscErr :: (?globals :: Globals) => CheckerError -> MaybeT Checker EqualityResult
miscErr = equalityErr


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


-- | The current form.
type EqualityResultWithType = (Bool, Type, Substitution)



-- | Wrangle an EqualityResult into the form currently used by other modules.
toCurrentForm :: (?globals :: Globals) => Type -> MaybeT Checker EqualityResult -> MaybeT Checker EqualityResultWithType
toCurrentForm t em = do
  e <- em
  withTy <- eqSubproof e $ (\(c,u) -> do
                              t' <- substitute u t
                              pure . pure $ (t', c, u))
  either (const $ pure (False, t, [])) (\(t', cs, u) -> mapM_ addConstraint cs >> pure (True, t', u)) withTy


-- | Get the substitution from an equality result.
equalitySubstitution :: EqualityResult -> Either InequalityReason Substitution
equalitySubstitution = fmap equalityProofSubstitution


-- | Equality where nothing needs to be done.
trivialEquality :: MaybeT Checker EqualityResult
trivialEquality = pure $ Right ([], [])


-- | Attempt to prove equality using the result of a previous proof.
eqSubproof :: (Monad m) => EqualityResult -> (EqualityProof -> m (Either InequalityReason a)) -> m (Either InequalityReason a)
eqSubproof e f = either (pure . Left) f e


-- | Require that two proofs of equality hold, and if so, combine them.
combinedEqualities :: (?globals :: Globals) => Span -> EqualityResult -> EqualityResult -> MaybeT Checker EqualityResult
combinedEqualities s e1 e2 =
  eqSubproof e1 $ \eq1res -> do
    eqSubproof e2 $ \eq2res -> do
      let u1 = equalityProofSubstitution eq1res
          u2 = equalityProofSubstitution eq2res
          cs = equalityProofConstraints eq1res
               <> equalityProofConstraints eq2res
      uf <- combineSubstitutions s u1 u2
      pure . pure $ (cs, uf)


-- | An equality under the given proof.
equalWith :: EqualityProof -> EqualityResult
equalWith = Right


---------------------------------
----- Bulk of equality code -----
---------------------------------


lEqualTypesWithPolarity :: (?globals :: Globals)
  => Span -> SpecIndicator ->Type -> Type -> MaybeT Checker EqualityResultWithType
lEqualTypesWithPolarity s pol = equalTypesRelatedCoeffectsAndUnify s ApproximatedBy pol

equalTypesWithPolarity :: (?globals :: Globals)
  => Span -> SpecIndicator -> Type -> Type -> MaybeT Checker EqualityResultWithType
equalTypesWithPolarity s pol = equalTypesRelatedCoeffectsAndUnify s Eq pol

lEqualTypes :: (?globals :: Globals)
  => Span -> Type -> Type -> MaybeT Checker EqualityResultWithType
lEqualTypes s = equalTypesRelatedCoeffectsAndUnify s ApproximatedBy SndIsSpec

equalTypes :: (?globals :: Globals)
  => Span -> Type -> Type -> MaybeT Checker EqualityResultWithType
equalTypes s = equalTypesRelatedCoeffectsAndUnify s Eq SndIsSpec

equalTypes' :: (?globals :: Globals)
  => Span -> Type -> Type -> MaybeT Checker EqualityResult
equalTypes' s t1 t2 = equalTypesRelatedCoeffects s Eq t1 t2 SndIsSpec

equalTypesWithUniversalSpecialisation :: (?globals :: Globals)
  => Span -> Type -> Type -> MaybeT Checker EqualityResultWithType
equalTypesWithUniversalSpecialisation s = equalTypesRelatedCoeffectsAndUnify s Eq SndIsSpec

{- | Check whether two types are equal, and at the same time
     generate coeffect equality constraints and unify the
     two types

     The first argument is taken to be possibly approximated by the second
     e.g., the first argument is inferred, the second is a specification
     being checked against
-}
equalTypesRelatedCoeffectsAndUnify :: (?globals :: Globals)
  => Span
  -- Explain how coeffects should be related by a solver constraint
  -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
  -- Starting spec indication
  -> SpecIndicator
  -- Left type (usually the inferred)
  -> Type
  -- Right type (usually the specified)
  -> Type
  -- Result is a effectful, producing:
  --    * a boolean of the equality
  --    * the most specialised type (after the unifier is applied)
  --    * the unifier
  -> MaybeT Checker EqualityResultWithType
equalTypesRelatedCoeffectsAndUnify s rel spec t1 t2 =
  toCurrentForm t2 $ equalTypesRelatedCoeffects s rel t1 t2 spec

data SpecIndicator = FstIsSpec | SndIsSpec | PatternCtxt
  deriving (Eq, Show)

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
  -> MaybeT Checker EqualityResult
equalTypesRelatedCoeffects s rel (FunTy t1 t2) (FunTy t1' t2') sp = do
  -- contravariant position (always approximate)
  eq1 <- equalTypesRelatedCoeffects s ApproximatedBy t1' t1 (flipIndicator sp)
  eq2 <- eqSubproof eq1 $ \eqres -> do
           let u1 = equalityProofSubstitution eqres
           -- covariant position (depends: is not always over approximated)
           t2 <- substitute u1 t2
           t2' <- substitute u1 t2'
           equalTypesRelatedCoeffects s rel t2 t2' sp
  combinedEqualities s eq1 eq2

equalTypesRelatedCoeffects s _ (TyCon con1) (TyCon con2) _ =
  directEqualityTest "Type constructors" s con1 con2

-- THE FOLLOWING FOUR CASES ARE TEMPORARY UNTIL WE MAKE 'Effect' RICHER

-- Over approximation by 'IO' "monad"
equalTypesRelatedCoeffects s rel (Diamond ef t1) (Diamond ["IO"] t2) sp
    = equalTypesRelatedCoeffects s rel t1 t2 sp

-- Under approximation by 'IO' "monad"
equalTypesRelatedCoeffects s rel (Diamond ["IO"] t1) (Diamond ef t2) sp
    = equalTypesRelatedCoeffects s rel t1 t2 sp

-- Over approximation by 'Session' "monad"
equalTypesRelatedCoeffects s rel (Diamond ef t1) (Diamond ["Session"] t2) sp
    | "Com" `elem` ef || null ef
      = equalTypesRelatedCoeffects s rel t1 t2 sp

-- Under approximation by 'Session' "monad"
equalTypesRelatedCoeffects s rel (Diamond ["Session"] t1) (Diamond ef t2) sp
    | "Com" `elem` ef || null ef
      = equalTypesRelatedCoeffects s rel t1 t2 sp

equalTypesRelatedCoeffects s rel (Diamond ef1 t1) (Diamond ef2 t2) sp = do
  if ( ef1 == ef2
     -- Effect approximation
     || ef1 `isPrefixOf` ef2
     -- Communication effect analysis is idempotent
     || (nub ef1 == ["Com"] && nub ef2 == ["Com"]))
  then equalTypesRelatedCoeffects s rel t1 t2 sp
  else effectMismatch s ef1 ef2

equalTypesRelatedCoeffects s rel x@(Box c t) y@(Box c' t') sp = do
  -- Debugging messages
  debugM "equalTypesRelatedCoeffects (pretty)" $ pretty c <> " == " <> pretty c'
  debugM "equalTypesRelatedCoeffects (show)" $ "[ " <> show c <> " , " <> show c' <> "]"
  -- Unify the coeffect kinds of the two coeffects
  kind <- mguCoeffectTypes s c c'
  -- subst <- unify c c'
  eq1 <- case sp of
    SndIsSpec -> do
      pure $ equalWith ([rel s c c' kind], [])
    FstIsSpec -> do
      pure $ equalWith ([rel s c' c kind], [])
    _ -> contextDoesNotAllowUnification s x y
  eq2 <- equalTypesRelatedCoeffects s rel t t' sp
  combinedEqualities s eq1 eq2

equalTypesRelatedCoeffects s _ (TyVar n) (TyVar m) _ | n == m = do
  checkerState <- get
  case lookup n (tyVarContext checkerState) of
    Just _ -> trivialEquality
    Nothing -> miscErr $ UnboundVariableError (Just s) ("Type variable " <> pretty n)

equalTypesRelatedCoeffects s _ (TyVar n) (TyVar m) sp = do
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
      tyVarConstraint (k2, m) (k1, n)


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
        tyVarConstraint (k2, m) (k1, n)

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

          k <- inferKindOfType s (TyCon kc)
          -- Create solver vars for coeffects
          case k of
            KCoeffect -> addConstraint (Eq s (CVar n) (CVar m) (TyCon kc))
            _         -> return ()

          pure $ equalWith ([], [(m, SubstT $ TyVar n)])
        Just _ ->
          pure $ equalWith ([], [(m, SubstT $ TyVar n)])
        Nothing -> unequalNotSpecified s n m


-- Duality is idempotent (left)
equalTypesRelatedCoeffects s rel (TyApp (TyCon d') (TyApp (TyCon d) t)) t' sp
  | internalName d == "Dual" && internalName d' == "Dual" =
  equalTypesRelatedCoeffects s rel t t' sp

-- Duality is idempotent (right)
equalTypesRelatedCoeffects s rel t (TyApp (TyCon d') (TyApp (TyCon d) t')) sp
  | internalName d == "Dual" && internalName d' == "Dual" =
  equalTypesRelatedCoeffects s rel t t' sp

equalTypesRelatedCoeffects s rel (TyVar n) t sp = do
  checkerState <- get
  debugM "Types.equalTypesRelatedCoeffects on TyVar"
          $ "span: " <> show s
          <> "\nTyVar: " <> show n <> " with " <> show (lookup n (tyVarContext checkerState))
          <> "\ntype: " <> show t <> "\nspec indicator: " <> show sp
  case lookup n (tyVarContext checkerState) of
    -- We can unify an instance with a concrete type
    (Just (k1, q)) | (q == BoundQ) || (q == InstanceQ && sp /= PatternCtxt) -> do
      k2 <- inferKindOfType s t
      case k1 `joinKind` k2 of
        Nothing -> illKindedUnifyVar s (TyVar n) k1 t k2

        -- If the kind is Nat, then create a solver constraint
        Just (KPromote (TyCon (internalName -> "Nat"))) -> do
          nat <- compileNatKindedTypeToCoeffect s t
          pure $ equalWith ([Eq s (CVar n) nat (TyCon $ mkId "Nat")], [(n, SubstT t)])

        Just _ -> pure $ equalWith ([], [(n, SubstT t)])

    -- NEW

    (Just (k1, ForallQ)) -> do
       -- Infer the kind of this equality
       k2 <- inferKindOfType s t
       let kind = k1 `joinKind` k2

       -- If the kind if nat then set up and equation as there might be a
       -- pausible equation involving the quantified variable
       if (kind == Just (KPromote (TyCon (Id "Nat" "Nat"))))
         then do
           c1 <- compileNatKindedTypeToCoeffect s (TyVar n)
           c2 <- compileNatKindedTypeToCoeffect s t
           pure $ equalWith ([Eq s c1 c2 (TyCon $ mkId "Nat")], [(n, SubstT t)])

         else cannotUnifyUniversalWithConcrete s n kind t

    (Just (_, InstanceQ)) -> error "Please open an issue at https://github.com/dorchard/granule/issues"
    (Just (_, BoundQ)) -> error "Please open an issue at https://github.com/dorchard/granule/issues"
    Nothing -> miscErr $ UnboundVariableError (Just s) (pretty n <?> ("Types.equalTypesRelatedCoeffects: " <> show (tyVarContext checkerState)))


equalTypesRelatedCoeffects s rel t (TyVar n) sp =
  equalTypesRelatedCoeffects s rel (TyVar n) t (flipIndicator sp)

-- Do duality check (left) [special case of TyApp rule]
equalTypesRelatedCoeffects s rel (TyApp (TyCon d) t) t' sp
  | internalName d == "Dual" = isDualSession s rel t t' sp

equalTypesRelatedCoeffects s rel t (TyApp (TyCon d) t') sp
  | internalName d == "Dual" = isDualSession s rel t t' sp

-- Equality on type application
equalTypesRelatedCoeffects s rel (TyApp t1 t2) (TyApp t1' t2') sp = do
  eq1 <- equalTypesRelatedCoeffects s rel t1 t1' sp
  eq2 <- eqSubproof eq1 (\eqres -> do
           let u1 = equalityProofSubstitution eqres
           t2 <- substitute u1 t2
           t2' <- substitute u1 t2'
           equalTypesRelatedCoeffects s rel t2 t2' sp)
  combinedEqualities s eq1 eq2


equalTypesRelatedCoeffects s rel t1 t2 t = do
  debugM "equalTypesRelatedCoeffects" $ "called on: " <> show t1 <> "\nand:\n" <> show t2
  equalOtherKindedTypesGeneric s t1 t2

{- | Equality on other types (e.g. Nat and Session members) -}
equalOtherKindedTypesGeneric :: (?globals :: Globals)
    => Span
    -> Type
    -> Type
    -> MaybeT Checker EqualityResult
equalOtherKindedTypesGeneric s t1 t2 = do
  k1 <- inferKindOfType s t1
  k2 <- inferKindOfType s t2
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
    => Span -> Type -> Type -> MaybeT Checker EqualityResult
sessionInequality s (TyApp (TyCon c) t) (TyApp (TyCon c') t')
  | internalName c == "Send" && internalName c' == "Send" = do
  equalTypes' s t t'

sessionInequality s (TyApp (TyCon c) t) (TyApp (TyCon c') t')
  | internalName c == "Recv" && internalName c' == "Recv" = do
  equalTypes' s t t'

sessionInequality s (TyCon c) (TyCon c')
  | internalName c == "End" && internalName c' == "End" =
  trivialEquality

sessionInequality s t1 t2 = unequalSessionTypes s t1 t2

isDualSession :: (?globals :: Globals)
    => Span
       -- Explain how coeffects should be related by a solver constraint
    -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
    -> Type
    -> Type
    -- Indicates whether the first type or second type is a specification
    -> SpecIndicator
    -> MaybeT Checker EqualityResult
isDualSession sp rel (TyApp (TyApp (TyCon c) t) s) (TyApp (TyApp (TyCon c') t') s') ind
  |  (internalName c == "Send" && internalName c' == "Recv")
  || (internalName c == "Recv" && internalName c' == "Send") = do
  eq1 <- equalTypesRelatedCoeffects sp rel t t' ind
  eq2 <- isDualSession sp rel s s' ind
  combinedEqualities sp eq1 eq2

isDualSession _ _ (TyCon c) (TyCon c') _
  | internalName c == "End" && internalName c' == "End" =
  trivialEquality

isDualSession sp rel t (TyVar v) ind =
  equalTypesRelatedCoeffects sp rel (TyApp (TyCon $ mkId "Dual") t) (TyVar v) ind

isDualSession sp rel (TyVar v) t ind =
  equalTypesRelatedCoeffects sp rel (TyVar v) (TyApp (TyCon $ mkId "Dual") t) ind

isDualSession sp _ t1 t2 _ = sessionsNotDual sp t1 t2


-- Essentially equality on types but join on any coeffects
joinTypes :: (?globals :: Globals) => Span -> Type -> Type -> MaybeT Checker Type

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
      else effectMismatch s ef ef' >>= either halt (pure . const t')

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

joinTypes s t1 t2 = do
  halt $ GenericError (Just s)
    $ "Type '" <> pretty t1 <> "' and '"
               <> pretty t2 <> "' have no upper bound"
