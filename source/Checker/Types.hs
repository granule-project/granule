{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ImplicitParams #-}

module Checker.Types where

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Data.List

import Checker.Coeffects
import Checker.Kinds
import Checker.Monad
import Checker.Predicates
import Checker.Substitutions
import Syntax.Expr
import Syntax.Pretty
import Utils

lEqualTypes :: (?globals :: Globals )
  => Span -> Type -> Type -> MaybeT Checker (Bool, Type, Substitution)
lEqualTypes s = equalTypesRelatedCoeffectsAndUnify s Leq False

equalTypes :: (?globals :: Globals )
  => Span -> Type -> Type -> MaybeT Checker (Bool, Type, Substitution)
equalTypes s = equalTypesRelatedCoeffectsAndUnify s Eq False

equalTypesWithUniversalSpecialisation :: (?globals :: Globals )
  => Span -> Type -> Type -> MaybeT Checker (Bool, Type, Substitution)
equalTypesWithUniversalSpecialisation s = equalTypesRelatedCoeffectsAndUnify s Eq True

{- | Check whether two types are equal, and at the same time
     generate coeffect equality constraints and unify the
     two types

     The first argument is taken to be possibly approximated by the second
     e.g., the first argument is inferred, the second is a specification
     being checked against
-}
equalTypesRelatedCoeffectsAndUnify :: (?globals :: Globals )
  => Span
  -- Explain how coeffects should be related by a solver constraint
  -> (Span -> Coeffect -> Coeffect -> CKind -> Constraint)
  -- Whether to allow universal specialisation
  -> Bool
  -- Left type (usually the inferred)
  -> Type
  -- Right type (usually the specified)
  -> Type
  -- Result is a effectful, producing:
  --    * a boolean of the equality
  --    * the most specialised type (after the unifier is applied)
  --    * the unifier
  -> MaybeT Checker (Bool, Type, Substitution)
equalTypesRelatedCoeffectsAndUnify s rel allowUniversalSpecialisation t1 t2 = do

   (eq, unif) <- equalTypesRelatedCoeffects s rel allowUniversalSpecialisation t1 t2 SndIsSpec
   if eq
     then do
        t2 <- substitute unif t2
        return (eq, t2, unif)
     else return (eq, t1, [])

data SpecIndicator = FstIsSpec | SndIsSpec
  deriving (Eq, Show)

flipIndicator FstIsSpec = SndIsSpec
flipIndicator SndIsSpec = FstIsSpec

{- | Check whether two types are equal, and at the same time
     generate coeffect equality constraints and a unifier
      Polarity indicates which -}
equalTypesRelatedCoeffects :: (?globals :: Globals )
  => Span
  -- Explain how coeffects should be related by a solver constraint
  -> (Span -> Coeffect -> Coeffect -> CKind -> Constraint)
  -> Bool -- whether to allow universal specialisation
  -> Type
  -> Type
  -- Indicates whether the first type or second type is a specification
  -> SpecIndicator
  -> MaybeT Checker (Bool, Substitution)
equalTypesRelatedCoeffects s rel uS (FunTy t1 t2) (FunTy t1' t2') sp = do
  -- contravariant position (always approximate)
  (eq1, u1) <- equalTypesRelatedCoeffects s Leq uS t1' t1 (flipIndicator sp)
   -- covariant position (depends: is not always over approximated)
  t2 <- substitute u1 t2
  t2' <- substitute u1 t2'
  (eq2, u2) <- equalTypesRelatedCoeffects s rel uS t2 t2' sp
  unifiers <- combineUnifiers s u1 u2
  return (eq1 && eq2, unifiers)

equalTypesRelatedCoeffects _ _ _ (TyCon con) (TyCon con') _ =
  return (con == con', [])

-- THE FOLLOWING TWO CASES ARE TEMPORARY UNTIL WE MAKE 'Effect' RICHER

-- Over approximation by 'FileIO' "monad"
equalTypesRelatedCoeffects s rel uS (Diamond ef t) (TyApp (TyCon con) t') sp
   | internalName con == "FileIO" = do
    (eq, unif) <- equalTypesRelatedCoeffects s rel uS t t' sp
    return (eq, unif)

-- Under approximation by 'FileIO' "monad"
equalTypesRelatedCoeffects s rel uS (TyApp (TyCon con) t') (Diamond ef t) sp
   | internalName con == "FileIO" = do
    (eq, unif) <- equalTypesRelatedCoeffects s rel uS t t' sp
    return (eq, unif)

-- Over approximation by 'Session' "monad"
equalTypesRelatedCoeffects s rel uS (Diamond ef t) (TyApp (TyCon con) t') sp
       | internalName con == "Session" && ("Com" `elem` ef || null ef) = do
        (eq, unif) <- equalTypesRelatedCoeffects s rel uS t t' sp
        return (eq, unif)

-- Under approximation by 'Session' "monad"
equalTypesRelatedCoeffects s rel uS (TyApp (TyCon con) t') (Diamond ef t) sp
       | internalName con == "Session" && ("Com" `elem` ef || null ef) = do
        (eq, unif) <- equalTypesRelatedCoeffects s rel uS t t' sp
        return (eq, unif)


equalTypesRelatedCoeffects s rel uS (Diamond ef t) (Diamond ef' t') sp = do
  (eq, unif) <- equalTypesRelatedCoeffects s rel uS t t' sp
  if ef == ef'
    then return (eq, unif)
    else
      -- Effect approximation
      if (ef `isPrefixOf` ef')
      then return (eq, unif)
      else halt $ GradingError (Just s) $
        "Effect mismatch: " ++ pretty ef ++ " not equal to " ++ pretty ef'

equalTypesRelatedCoeffects s rel uS (Box c t) (Box c' t') sp = do
  -- Debugging messages
  debugM "equalTypesRelatedCoeffects (pretty)" $ pretty c ++ " == " ++ pretty c'
  debugM "equalTypesRelatedCoeffects (show)" $ "[ " ++ show c ++ " , " ++ show c' ++ "]"
  -- Unify the coeffect kinds of the two coeffects
  kind <- mguCoeffectTypes s c c'
  addConstraint (rel s c c' kind)
  equalTypesRelatedCoeffects s rel uS t t' sp

equalTypesRelatedCoeffects s rel uS (TyApp t1 t2) (TyApp t1' t2') sp = do
  (one, u1) <- equalTypesRelatedCoeffects s rel uS t1 t1' sp
  t2  <- substitute u1 t2
  t2' <- substitute u1 t2'
  (two, u2) <- equalTypesRelatedCoeffects s rel uS t2 t2' sp
  unifiers <- combineUnifiers s u1 u2
  return (one && two, unifiers)

equalTypesRelatedCoeffects s _ _ (TyVar n) (TyVar m) _ | n == m = do
  checkerState <- get
  case lookup n (tyVarContext checkerState) of
    Just _ -> return (True, [])
    Nothing -> halt $ UnboundVariableError (Just s) ("Type variable " ++ pretty n)

equalTypesRelatedCoeffects s _ _ (TyVar n) (TyVar m) sp = do
  checkerState <- get

  case (lookup n (tyVarContext checkerState), lookup m (tyVarContext checkerState)) of

    -- Two universally quantified variables are unequal
    (Just (_, ForallQ), Just (_, ForallQ)) ->
        return (False, [])

    -- We can unify a universal a dependently bound universal
    (Just (k1, ForallQ), Just (k2, BoundQ)) | sp == FstIsSpec ->
      tyVarConstraint k1 k2 n m

    (Just (k1, BoundQ), Just (k2, ForallQ)) | sp == SndIsSpec ->
      tyVarConstraint k1 k2 n m

    -- We can unify two instance type variables
    (Just (k1, InstanceQ), Just (k2, BoundQ)) ->
        tyVarConstraint k1 k2 n m

    -- We can unify two instance type variables
    (Just (k1, BoundQ), Just (k2, InstanceQ)) ->
        tyVarConstraint k1 k2 n m

    -- We can unify two instance type variables
    (Just (k1, InstanceQ), Just (k2, InstanceQ)) ->
      tyVarConstraint k1 k2 n m

    -- But we can unify a forall and an instance
    (Just (k1, InstanceQ), Just (k2, ForallQ)) ->
      tyVarConstraint k1 k2 n m

    -- But we can unify a forall and an instance
    (Just (k1, ForallQ), Just (k2, InstanceQ)) ->
      tyVarConstraint k1 k2 n m

    -- Trying to unify other (existential) variables
    (Just (KType, _), Just (k, _)) | k /= KType -> do
      k <- inferKindOfType s (TyVar m)
      illKindedUnifyVar s (TyVar n) KType (TyVar m) k

    (Just (k, _), Just (KType, _)) | k /= KType -> do
      k <- inferKindOfType s (TyVar n)
      illKindedUnifyVar s (TyVar n) k (TyVar m) KType

    -- Otherwise
    --(Just (k1, _), Just (k2, _)) ->
    --  tyVarConstraint k1 k2 n m

    (t1, t2) -> error $ pretty s ++ "-" ++ show sp ++ "\n" ++ pretty n ++ " : " ++ show t1 ++ "\n" ++ pretty m ++ " : " ++ show t2
  where
    tyVarConstraint k1 k2 n m = do
      case k1 `joinKind` k2 of
        Just (KConstr kc) -> do
          addConstraint (Eq s (CVar n) (CVar m) (CConstr kc))
          return (True, [(n, SubstT $ TyVar m)])
        Just _ ->
          return (True, [(n, SubstT $ TyVar m)])
        Nothing ->
          return (False, [])

equalTypesRelatedCoeffects s rel uS (PairTy t1 t2) (PairTy t1' t2') sp = do
  (lefts, u1)  <- equalTypesRelatedCoeffects s rel uS t1 t1' sp
  t2  <- substitute u1 t2
  t2' <- substitute u1 t2'
  (rights, u2) <- equalTypesRelatedCoeffects s rel uS t2 t2' sp
  unifiers <- combineUnifiers s u1 u2
  return (lefts && rights, unifiers)

equalTypesRelatedCoeffects s rel allowUniversalSpecialisation (TyVar n) t sp = do
  checkerState <- get
  debugM "Types.equalTypesRelatedCoeffects on TyVar"
          $ "span: " ++ show s
          ++ "\nallowUniversalSpecialisation: " ++ show allowUniversalSpecialisation
          ++ "\nTyVar: " ++ show n ++ "\ntype: " ++ show t ++ "\nspec indicator: " ++ show sp
  case lookup n (tyVarContext checkerState) of
    -- We can unify an instance with a concrete type
    (Just (k1, q)) | q == InstanceQ || q == BoundQ -> do
      k2 <- inferKindOfType s t
      case k1 `joinKind` k2 of
        Nothing -> illKindedUnifyVar s (TyVar n) k1 t k2

        -- If the kind is Nat=, then create a solver constraint
        Just (KConstr k) | internalName k == "Nat=" -> do
          nat <- compileNatKindedTypeToCoeffect s t
          addConstraint (Eq s (CVar n) nat (CConstr $ mkId "Nat="))
          return (True, [(n, SubstT t)])

        Just _ -> return (True, [(n, SubstT t)])

    -- Unifying a forall with a concrete type may only be possible if the concrete
    -- type is exactly equal to the forall-quantified variable
    -- This can only happen for nat indexed types at the moment via the
    -- additional equations so performa an additional check if they
    -- are both of Nat kind
    (Just (k1, ForallQ)) -> do
      k1 <- inferKindOfType s (TyVar n)
      k2 <- inferKindOfType s t
      case (k1, k2) of
        (KConstr k1, KConstr k2) | internalName k1 == "Nat=" && internalName k2 == "Nat=" -> do
          c1 <- compileNatKindedTypeToCoeffect s (TyVar n)
          c2 <- compileNatKindedTypeToCoeffect s t
          addConstraint $ Eq s c1 c2 (CConstr $ mkId "Nat=")
          return (True, [(n, SubstT t)])
        x ->
          if allowUniversalSpecialisation
            then
              return (True, [(n, SubstT t)])
            else
            halt $ GenericError (Just s)
            $ case sp of
             FstIsSpec -> "Trying to match a polymorphic type '" ++ pretty n
                       ++ "' with monomorphic " ++ pretty t
             SndIsSpec -> pretty t ++ " is not equal to " ++ pretty (TyVar n)

    (Just (_, InstanceQ)) -> error "Please open an issue at https://github.com/dorchard/granule/issues"
    (Just (_, BoundQ)) -> error "Please open an issue at https://github.com/dorchard/granule/issues"
    Nothing -> halt $ UnboundVariableError (Just s) (pretty n <?> ("Types.equalTypesRelatedCoeffects: " ++ show (tyVarContext checkerState)))

equalTypesRelatedCoeffects s rel uS t (TyVar n) sp =
  equalTypesRelatedCoeffects s rel uS (TyVar n) t (flipIndicator sp)

equalTypesRelatedCoeffects s rel uS t1 t2 t = do
  debugM "equalTypesRelatedCoeffects" $ "called on: " ++ show t1 ++ "\nand:\n" ++ show t2
  equalOtherKindedTypesGeneric s t1 t2

{- | Check whether two Nat-kinded types are equal -}
equalOtherKindedTypesGeneric :: (?globals :: Globals )
    => Span
    -> Type
    -> Type
    -> MaybeT Checker (Bool, Substitution)
equalOtherKindedTypesGeneric s t1 t2 = do
  k1 <- inferKindOfType s t1
  k2 <- inferKindOfType s t2
  case (k1, k2) of
    (KConstr n, KConstr n')
      | "Nat" `isPrefixOf` (internalName n) && "Nat" `isPrefixOf` (internalName  n') -> do
        c1 <- compileNatKindedTypeToCoeffect s t1
        c2 <- compileNatKindedTypeToCoeffect s t2
        addConstraint $ Eq s c1 c2 (CConstr $ mkId "Nat=")
        return (True, [])
    (KType, KType) ->
       halt $ GenericError (Just s) $ pretty t1 ++ " is not equal to " ++ pretty t2

    (KConstr n, KConstr n') | internalName n == "Session" && internalName n' == "Session" ->
       sessionEquality s t1 t2
    _ ->
       halt $ KindError (Just s) $ "Equality is not defined between kinds "
                 ++ pretty k1 ++ " and " ++ pretty k2
                 ++ "\t\n from equality "
                 ++ "'" ++ pretty t2 ++ "' and '" ++ pretty t1 ++ "' equal."

sessionEquality :: (?globals :: Globals)
    => Span -> Type -> Type -> MaybeT Checker (Bool, Substitution)
sessionEquality s (TyApp (TyCon c) t) (TyApp (TyCon c') t')
  | internalName c == "Send" && internalName c' == "Send" = do
  (g, _, u) <- equalTypes s t t'
  return (g, u)

sessionEquality s (TyApp (TyCon c) t) (TyApp (TyCon c') t')
  | internalName c == "Recv" && internalName c' == "Recv" = do
  (g, _, u) <- equalTypes s t t'
  return (g, u)

sessionEquality s (TyCon c) (TyCon c')
  | internalName c == "End" && internalName c' == "End" =
  return (True, [])

sessionEquality s t1 t2 =
  halt $ GenericError (Just s)
       $ "Session type '" ++ pretty t1 ++ "' is not equal to '" ++ pretty t2 ++ "'"

combineUnifiers ::
  (?globals :: Globals)
  => Span -> Substitution -> Substitution -> MaybeT Checker Substitution
combineUnifiers s u1 u2 = do
    -- For all things in the (possibly empty) intersection of contexts `u1` and `u2`,
    -- check whether things can be unified, i.e. exactly
    uss1 <- forM u1 $ \(v, s) ->
      case lookupMany v u2 of
        -- Unifier in u1 but not in u2
        [] -> return [(v, s)]
        -- Possible unificaitons in each part
        alts -> do
            unifs <-
              forM alts $ \s' ->
                 --(us, t) <- unifiable v t t' t t'
                 case unify s s' of
                   Nothing -> error "Cannot unify"
                   Just us -> do
                     sUnified <- substitute us s
                     return $ (v, sUnified) : us

            return $ concat unifs
    -- Any remaining unifiers that are in u2 but not u1
    uss2 <- forM u2 $ \(v, s) ->
       case lookup v u1 of
         Nothing -> return [(v, s)]
         _       -> return []
    return $ concat uss1 ++ concat uss2

{-
  where
    -- A type varible unifies with anything, including another type variable
    unifiable _ _ _ (SubstT (TyVar v)) t = return ([(v, t)], t)
    unifiable _ _ _ t (SubstT (TyVar v)) = return ([(v, t)], t)

    -- The following cases unpeel constructors to see if we hit unifiables things inside
    unifiable var t1 t2 (Box c t) (Box c' t') = do
      (usC, c'') <- unifiable_Coeff var t1 t2 c c'
      (us', t') <- unifiable var t1 t2 t t'
      return (us', Box (substitute usC c'') t')

    unifiable _ _ __ _ t = return ([], t)
    -- TODO: re-instate error case when needed
    --unifiable var t1 t2 _ _ = halt $ GenericError (Just s) (msg var t1 t2)


{- TODO: fill in rest along the same lines
    unifiable (Diamond e t) (Diamond e' t') =
      e == e' && unifiable t t'
    unifiable (PairTy t1 t2) (PairTy t1' t2') =

      unifiable t1 t1' && unifiable t2 t2'
    unifiable (FunTy t1 t2) (FunTy t1' t2') =
      unifiable t1 t1' && unifiable t2 t2'
    unifiable (TyInfix op t1 t2) (TyInfix op' t1' t2') =
      op == op' && unifiable t1 t1' && unifiable t2 t2'

    -- If none of the above hold, there is a mismatch between both contexts
    -- so we can't unify and throw a type error
    unifiable _ _ = False
    -}

    -- The same pattern holds for coeffects
    unifiable_Coeff _ _ _ (CVar v) c = return ([(v, c)], c)

    unifiable_Coeff _ _ _ c (CVar v) = return ([(v, c)], c)

    unifiable_Coeff var t1 t2 (CPlus c1 c2) (CPlus c1' c2') = do
      (us1, c1u) <- unifiable_Coeff var t1 t2 c1 c1'
      (us2, c2u) <- unifiable_Coeff var t1 t2 c2 c2'
      return $ (us1 ++ us2, CPlus c1u c2u)

    unifiable_Coeff var t1 t2 (CTimes c1 c2) (CTimes c1' c2') = do
      (us1, c1u) <- unifiable_Coeff var t1 t2 c1 c1'
      (us2, c2u) <- unifiable_Coeff var t1 t2 c2 c2'
      return $ (us1 ++ us2, CTimes c1u c2u)

    unifiable_Coeff var t1 t2 (CMeet c1 c2) (CMeet c1' c2') = do
      (us1, c1u) <- unifiable_Coeff var t1 t2 c1 c1'
      (us2, c2u) <- unifiable_Coeff var t1 t2 c2 c2'
      return $ (us1 ++ us2, CMeet c1u c2u)

    unifiable_Coeff var t1 t2 (CJoin c1 c2) (CJoin c1' c2') = do
      (us1, c1u) <- unifiable_Coeff var t1 t2 c1 c1'
      (us2, c2u) <- unifiable_Coeff var t1 t2 c2 c2'
      return $ (us1 ++ us2, CJoin c1u c2u)

    unifiable_Coeff var t1 t2 (CZero k) (CZero k') = do
      us <- unifiable_CKind var t1 t2 k k'
      kind <- substitute us k
      return $ ([], CZero kind)

    unifiable_Coeff var t1 t2 (COne k) (COne k') = do
      us <- unifiable_CKind var t1 t2 k k'
      kind <- substitute us k
      return $ ([], COne kind)

    unifiable_Coeff var t1 t2 (CInfinity k) (CInfinity k') = do
      us <- unifiable_CKind var t1 t2 k k'
      kind <- substitute us k
      return $ ([], CInfinity kind)

    unifiable_Coeff var t1 t2 _ _     =
      halt $ GenericError (Just s) (msg var t1 t2)

    -- ... and for coeffect kinds
    unifiable_CKind _ _ _ (CPoly v) k = do
      --modify (\st -> st { kVarContext = (v, k) : kVarContext st })
      return [(v, k)]

    unifiable_CKind _ _ _ k (CPoly v) = do
      --modify (\st -> st { kVarContext = (v, k) : kVarContext st })
      return [(v, k)]

    unifiable_CKind var t1 t2 k k' =
      if k == k'
        then return []
        else halt $ GenericError (Just s) (msg var t1 t2)

    msg k v1 v2 =
      "Type variable " ++ sourceName k
        ++ " cannot be unified to `" ++ pretty v1 ++ "` and `" ++ pretty v2
        ++ "` at the same time."
-}

-- Essentially equality on types but join on any coeffects
joinTypes :: (?globals :: Globals) => Span -> Type -> Type -> MaybeT Checker Type
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
      else halt $ GradingError (Just s) $
        "Effect mismatch: " ++ pretty ef ++ " not equal to " ++ pretty ef'

joinTypes s (Box c t) (Box c' t') = do
  kind <- mguCoeffectTypes s c c'
  -- Create a fresh coeffect variable
  topVar <- freshCoeffectVar (mkId "") kind
  -- Unify the two coeffects into one
  addConstraint (Leq s c  (CVar topVar) kind)
  addConstraint (Leq s c' (CVar topVar) kind)
  tu <- joinTypes s t t'
  return $ Box (CVar topVar) tu

joinTypes _ (TyInt n) (TyInt m) | n == m = return $ TyInt n

joinTypes s (TyInt n) (TyVar m) = do
  -- Create a fresh coeffect variable
  let kind = CConstr $ mkId "Nat="
  var <- freshCoeffectVar m kind
  -- Unify the two coeffects into one
  addConstraint (Eq s (CNat Discrete n) (CVar var) kind)
  return $ TyInt n

joinTypes s (TyVar n) (TyInt m) = joinTypes s (TyInt m) (TyVar n)

joinTypes s (TyVar n) (TyVar m) = do
  -- Create fresh variables for the two tyint variables
  let kind = CConstr $ mkId "Nat="
  nvar <- freshCoeffectVar n kind
  mvar <- freshCoeffectVar m kind
  -- Unify the two variables into one
  addConstraint (Leq s (CVar nvar) (CVar mvar) kind)
  return $ TyVar n

joinTypes s (TyApp t1 t2) (TyApp t1' t2') = do
  t1'' <- joinTypes s t1 t1'
  t2'' <- joinTypes s t2 t2'
  return (TyApp t1'' t2'')

joinTypes s (PairTy t1 t2) (PairTy t1' t2') = do
  t1'' <- joinTypes s t1 t1'
  t2'' <- joinTypes s t2 t2'
  return (PairTy t1'' t2'')

joinTypes s t1 t2 = do
  halt $ GenericError (Just s)
    $ "Type '" ++ pretty t1 ++ "' and '"
               ++ pretty t2 ++ "' have no upper bound"
