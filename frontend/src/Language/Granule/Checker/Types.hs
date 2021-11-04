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
import Data.List (sortBy)

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

import Language.Granule.Utils

import Data.Functor.Const

lEqualTypesWithPolarity :: (?globals :: Globals)
  => Span -> SpecIndicator -> Type -> Type -> Checker (Bool, Type, Substitution)
lEqualTypesWithPolarity s pol = equalTypesRelatedCoeffectsAndUnify s ApproximatedBy pol

equalTypesWithPolarity :: (?globals :: Globals)
  => Span -> SpecIndicator -> Type -> Type -> Checker (Bool, Type, Substitution)
equalTypesWithPolarity s pol = equalTypesRelatedCoeffectsAndUnify s Eq pol

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

{- | Check whether two types are equal, and at the same time
     generate (in)equality constraints and perform unification.

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
  let (t1', t2') = if spec == FstIsSpec then (t1, t2) else (t2, t1)
  -- Infer kinds
  (k, subst, _) <- synthKind s t1'
  (subst', _) <- checkKind s t2' k
  (eqT, subst'') <- equalTypesRelatedCoeffectsInner s rel t1 t2 k spec mode
  substFinal <- combineManySubstitutions s [subst,subst',subst'']
  return (eqT, substFinal)

equalTypesRelatedCoeffectsInner :: (?globals :: Globals)
  => Span
  -- Explain how coeffects should be related by a solver constraint
  -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
  -> Type
  -> Type
  -> Type
  -- Indicates whether the first type or second type is a specification
  -> SpecIndicator
  -- Flag to say whether this type is actually an effect or not
  -> Mode
  -> Checker (Bool, Substitution)

-- Base equality (helps to make things fast here)
equalTypesRelatedCoeffectsInner s rel t1 t2 _ _ _ | t1 == t2 =
  return (True, [])

equalTypesRelatedCoeffectsInner s rel fTy1@(FunTy _ t1 t2) fTy2@(FunTy _ t1' t2') _ sp mode = do
  debugM "equalTypesRelatedCoeffectsInner (funTy left)" ""
  -- contravariant position (always approximate)
  (eq1, u1) <- equalTypesRelatedCoeffects s ApproximatedBy t1' t1 (flipIndicator sp) mode
   -- covariant position (depends: is not always over approximated)
  t2 <- substitute u1 t2
  t2' <- substitute u1 t2'
  debugM "equalTypesRelatedCoeffectsInner (funTy right)" (pretty t2 <> " == " <> pretty t2')
  (eq2, u2) <- equalTypesRelatedCoeffects s rel t2 t2' sp mode
  unifiers <- combineSubstitutions s u1 u2
  return (eq1 && eq2, unifiers)

equalTypesRelatedCoeffectsInner _ _ (TyCon con1) (TyCon con2) _ _ _
  | internalName con1 /= "Pure" && internalName con2 /= "Pure" =
  return (con1 == con2, [])

equalTypesRelatedCoeffectsInner s rel (Diamond ef1 t1) (Diamond ef2 t2) _ sp Types = do
  debugM "equalTypesRelatedCoeffectsInner (diamond)" $ "grades " <> show ef1 <> " and " <> show ef2
  (eq, unif) <- equalTypesRelatedCoeffects s rel t1 t2 sp Types
  (eq', unif') <- equalTypesRelatedCoeffects s rel (handledNormalise s (Diamond ef1 t1) ef1) (handledNormalise s (Diamond ef2 t2) ef2) sp Effects
  u <- combineSubstitutions s unif unif'
  return (eq && eq', u)

equalTypesRelatedCoeffectsInner s rel (Star g1 t1) (Star g2 t2) _ sp mode = do
  (eq, unif) <- equalTypesRelatedCoeffects s rel t1 t2 sp mode
  (eq', _, unif') <- equalTypes s g1 g2
  u <- combineSubstitutions s unif unif'
  return (eq && eq', u)

equalTypesRelatedCoeffectsInner s rel x@(Box c t) y@(Box c' t') k sp Types = do
  -- Debugging messages
  debugM "equalTypesRelatedCoeffectsInner (box)" $ "grades " <> show c <> " and " <> show c' <> ""

  -- Unify the coeffect kinds of the two coeffects
  (kind, subst, (inj1, inj2)) <- mguCoeffectTypesFromCoeffects s c c'

  -- Add constraint for the coeffect (using ^op for the ordering compared with the order of equality)
  c' <- substitute subst c'
  c  <- substitute subst c
  kind <- substitute subst kind
  addConstraint (rel s (inj2 c') (inj1 c) kind)

  -- Create a substitution if we can (i.e., if this is an equality and one grade is a variable)
  -- as this typically greatly improves error messages and repl interaction
  let substExtra =
       if isEq (rel s undefined undefined undefined)
          then
            case c of
              TyVar v -> [(v, SubstT c')]
              _ -> case c' of
                    TyVar v -> [(v, SubstT c)]
                    _       -> []
          else
            []

  (eq, subst') <- equalTypesRelatedCoeffects s rel t t' sp Types

  substU <- combineManySubstitutions s [subst, subst', substExtra]
  return (eq, substU)

equalTypesRelatedCoeffectsInner s rel (TyVar var1) ty _ _ _ = do
  subst <- unification s var1 ty rel
  return (True, subst)

equalTypesRelatedCoeffectsInner s rel ty (TyVar var2) _ _ _ = do
  subst <- unification s var2 ty rel
  return (True, subst)


{- -- TODO: DEL
equalTypesRelatedCoeffectsInner s _ (TyVar n) (TyVar m) _ _ mode | n == m = do
  checkerState <- get
  case lookup n (tyVarContext checkerState) of
    Just _ -> return (True, [])
    Nothing -> throw UnboundTypeVariable { errLoc = s, errId = n }

equalTypesRelatedCoeffectsInner s _ (TyVar n) (TyVar m) sp _ mode = do
  checkerState <- get
  debugM "variable equality" $ pretty n <> " ~ " <> pretty m <> " where "
                            <> pretty (lookup n (tyVarContext checkerState)) <> " and "
                            <> pretty (lookup m (tyVarContext checkerState))

  case (lookup n (tyVarContext checkerState), lookup m (tyVarContext checkerState)) of

    -- Two universally quantified variables are unequal
    (Just (_, ForallQ), Just (_, ForallQ)) ->
        return (False, [])

    -- We can unify a universal a dependently bound universal
    (Just (k1, ForallQ), Just (k2, BoundQ)) ->
      tyVarConstraint (k2, m) (k1, n)

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
        tyVarConstraint (k2, m) (k1 , n)

    (t1, t2) -> error $ pretty s <> "-" <> show sp <> "\n"
              <> pretty n <> " : " <> show t1
              <> "\n" <> pretty m <> " : " <> show t2
  where
    tyVarConstraint (k1, n) (k2, m) = do
      jK <- joinTypes s k1 k2
      case jK of
        Just (TyCon kc, unif, _) -> do
          (result, putChecker) <- peekChecker (checkKind s (TyCon kc) kcoeffect)
          case result of
            Left err -> return ()
            -- Create solver vars for coeffects
            Right _ -> putChecker >> addConstraint (Eq s (TyVar n) (TyVar m) (TyCon kc))
          return (True, unif ++ [(n, SubstT $ TyVar m)])
        Just (_, unif, _) ->
          return (True, unif ++ [(n, SubstT $ TyVar m)])
        Nothing ->
          return (False, [])
-}

-- Duality is idempotent (left)
equalTypesRelatedCoeffectsInner s rel (TyApp (TyCon d') (TyApp (TyCon d) t)) t' k sp mode
  | internalName d == "Dual" && internalName d' == "Dual" =
  equalTypesRelatedCoeffectsInner s rel t t' k sp mode

-- Duality is idempotent (right)
equalTypesRelatedCoeffectsInner s rel t (TyApp (TyCon d') (TyApp (TyCon d) t')) k sp mode
  | internalName d == "Dual" && internalName d' == "Dual" =
  equalTypesRelatedCoeffectsInner s rel t t' k sp mode

{- -- TODO: DEL
equalTypesRelatedCoeffectsInner s rel (TyVar n) t kind sp mode = do
  checkerState <- get
  debugM "Types.equalTypesRelatedCoeffectsInner on TyVar"
          $ "span: " <> show s
          <> "\nkind: " <> show kind
          <> "\nTyVar: " <> show n <> " with " <> show (lookup n (tyVarContext checkerState))
          <> "\ntype: " <> show t <> "\nspec indicator: " <> show sp

  debugM "context" $ pretty $ tyVarContext checkerState

  -- Do an occurs check for types
  case kind of
    Type _ ->
       if n `elem` freeVars t
         then throw OccursCheckFail { errLoc = s, errVar = n, errTy = t }
         else return ()
    _ -> return ()

  case lookup n (tyVarContext checkerState) of
    -- We can unify an instance with a concrete type
    (Just (n_k, q)) | (q == BoundQ) || (q == InstanceQ) -> do --  && sp /= PatternCtxt

      jK <-  joinTypes s n_k kind
      case jK of
        Nothing -> throw UnificationKindError
          { errLoc = s, errTy1 = (TyVar n), errK1 = n_k, errTy2 = t, errK2 = kind }

        -- If the kind is Nat, then create a solver constraint
        -- TODO: generalise to things where the jk is of kind kcoeffect or keffect
         -- or jK is nat
        Just (TyCon (internalName -> "Nat"), subst, _) -> do
          addConstraint (Eq s (TyVar n) t (TyCon $ mkId "Nat"))
          subst' <- combineSubstitutions s subst [(n, SubstT t)]
          return (True, subst')

        Just (_, unif, _) -> return (True, unif ++ [(n, SubstT t)])

    (Just (n_k, ForallQ)) -> do

       -- If the kind is nat then set up an equation as there might be a
       -- plausible equation involving the quantified variable
       jK <- joinTypes s n_k kind
       case jK of
         -- TODO: generalise to things where the jk is of kind kcoeffect or keffect
         -- or jK is nat
         Just (TyCon (Id "Nat" "Nat"), unif, _) -> do
           addConstraint $ Eq s (TyVar n) t (TyCon $ mkId "Nat")
           return (True, [])

         _ -> throw UnificationFail{ errLoc = s, errVar = n, errKind = n_k, errTy = t, tyIsConcrete = True }

    (Just (_, InstanceQ)) -> error "Please open an issue at https://github.com/granule-project/granule/issues"
    (Just (_, BoundQ)) -> error "Please open an issue at https://github.com/granule-project/granule/issues"
    Nothing -> throw UnboundTypeVariable { errLoc = s, errId = n }


equalTypesRelatedCoeffectsInner s rel t (TyVar n) k sp mode =
  equalTypesRelatedCoeffectsInner s rel (TyVar n) t k (flipIndicator sp) mode
  -}

equalTypesRelatedCoeffectsInner s rel (Star g1 t1) t2 _ sp mode
  | t1 == t2 = throw $ UniquenessError { errLoc = s, uniquenessMismatch = NonUniqueUsedUniquely t2}
  | otherwise = do
    (g, _, u) <- equalTypes s t1 t2
    return (g, u)

equalTypesRelatedCoeffectsInner s rel t1 (Star g2 t2) k sp mode = 
  equalTypesRelatedCoeffectsInner s rel (Star g2 t2) t1 k (flipIndicator sp) mode

-- Do duality check (left) [special case of TyApp rule]
equalTypesRelatedCoeffectsInner s rel (TyApp (TyCon d) t) t' _ sp mode
  | internalName d == "Dual" = isDualSession s rel t t' sp

equalTypesRelatedCoeffectsInner s rel t (TyApp (TyCon d) t') _ sp mode
  | internalName d == "Dual" = isDualSession s rel t t' sp

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

equalTypesRelatedCoeffectsInner s rel t1 t2 k sp mode = do
  debugM "type Equality: Drop through case "
    ("t1 = " <> pretty t1 <> " t2 = " <> pretty t2 <> "\n k = " <> pretty k <> "\n mode = " <> show mode)
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
        (TyCon (internalName -> "Nat")) -> do
          debugM "equality on nats" (pretty t1 ++ " =? " ++ pretty t2)
          addConstraint $ Eq s t1 t2 (TyCon $ mkId "Nat")
          return (True, [])

        (TyCon (internalName -> "Protocol")) ->
          sessionInequality s t1 t2
        _ ->
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

-- | Find out if a type is indexed
isIndexedType :: Type -> Checker Bool
isIndexedType t = do
  b <- typeFoldM TypeFold
      { tfTy = \_ -> return $ Const False
      , tfFunTy = \_ (Const x) (Const y) -> return $ Const (x || y)
      , tfTyCon = \c -> do {
          st <- get;
          return $ Const $ case lookup c (typeConstructors st) of Just (_, _, isIndexed) -> isIndexed; Nothing -> False }
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
      , tfTySig = \(Const b) _ _ -> return $ Const b } t
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