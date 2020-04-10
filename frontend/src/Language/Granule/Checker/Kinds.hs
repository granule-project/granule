-- Mainly provides a kind checker on types
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Granule.Checker.Kinds (
                      inferKindOfType
                    , inferKindOfTypeInContext
                    , hasLub
                    , joinKind
                    , joinSort
                    , mguCoeffectTypesFromCoeffects
                    , inferCoeffectType
                    , inferCoeffectTypeInContext
                    , inferCoeffectTypeAssumption
                    , isEffectType
                    , isEffectKind
                    , isCoeffectKind) where

import Control.Monad.State.Strict

import Language.Granule.Checker.Flatten
import Language.Granule.Checker.KindsHelpers
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Primitives (tyOps, setElements)
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Variables

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Context
import Language.Granule.Utils

import Data.List (partition)

inferKindOfType :: (?globals :: Globals) => InferKind l => Span -> Type l -> Checker (Type (Succ l))
inferKindOfType s t = do
    checkerState <- get
    inferKindOfTypeInContext s (stripQuantifiers $ tyVarContext checkerState) t

class InferKind l where
  inferKindOfTypeInContext :: (?globals :: Globals) => Span -> Ctxt TypeWithLevel -> Type l -> Checker (Type (Succ l))

instance InferKind (Succ Zero) where
  inferKindOfTypeInContext s quantifiedVariables t = do
        w <- typeFoldM1 (TypeFoldOne kTy kFun kCon kVar kApp kInt kInfix kSet kCase) t
        return $ unwrap w
      where
        kTy :: ULevel Zero -> Checker Sort'
        kTy l = return $ W $ Type (LSucc l)

        kFun :: Sort' -> Sort' -> Checker Sort'
        kFun (W (TyCon c)) (W (TyCon c'))
          | internalName c == internalName c' = return $ W $ TyCon c

        kFun (W (Type l)) (W (Type l')) | l == l' = return $ W $ Type l
        kFun (W (Type l)) (W y) = throw SortMismatch{ errLoc = s, kActualS = Nothing, sExpected = Type l, sActual = y }
        kFun (W x) _     = throw SortMismatch{ errLoc = s, kActualS = Nothing, sExpected = Type (LSucc LZero), sActual = x }

        kCon :: Id -> Checker Sort'
        kCon (internalName -> "Pure") = do
          -- Create a fresh type variable
          var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") (TyCon (mkId "Effect"))
          return $ W $ TyVar var
        kCon conId = do
            st <- get
            case lookup conId (typeConstructors st) of
                Just (TypeWithLevel (LSucc (LSucc LZero)) sort,_,_) -> return $ W sort
                _   -> do
                  mConstructor <- lookupDataConstructor s conId
                  case mConstructor of
                    Just (Forall _ [] [] t, _) -> do
                      k <- tryTyPromote s t
                      sort <- tryTyPromote s k
                      return $ W sort
                    Just _ -> error $ pretty s <> "I'm afraid I can't yet promote the polymorphic data constructor:"  <> pretty conId
                    Nothing -> throw UnboundTypeConstructor{ errLoc = s, errId = conId }

        kVar :: Id -> Checker Sort'
        kVar tyVar =
          case lookup tyVar quantifiedVariables of
            Just (TypeWithLevel (LSucc (LSucc LZero)) sort) -> return $ W sort
            _   -> do
              st <- get
              case lookup tyVar (tyVarContext st) of
                Just (TypeWithLevel (LSucc (LSucc LZero)) sort, _) -> return $ W sort
                _ -> throw UnboundTypeVariable{ errLoc = s, errId = tyVar }

        kApp :: Sort' -> Sort' -> Checker Sort'
        kApp (W (FunTy k1 k2)) (W kArg) = do
          kLub <- k1 `sHasLub` kArg
          if kLub
            then return $ W k2
            else throw SortMismatch
                  { errLoc = s
                  , kActualS = Nothing
                  , sActual = kArg
                  , sExpected = k1 }

        kApp (W k) (W kArg) = throw SortMismatch
            { errLoc = s
            , kActualS = Nothing
            , sExpected = (FunTy kArg (TyVar $ mkId "..."))
            , sActual = k
            }

        kInt :: Int -> Checker Sort'
        kInt _ = return $ W $ TyCon $ mkId "Nat"

        kInfix :: TypeOperator -> Sort' -> Sort' -> Checker Sort'
        kInfix op (W sort) (W sort') = error $
          "Cannot currently do a kind-level infix operation " ++ pretty op
           ++ " on kinds of sort " ++ pretty sort ++ " and " ++ pretty sort'

        kSet :: [Sort'] -> Checker Sort'
        kSet wks = kSetW (map unwrap wks)

        kSetW :: [Type Two] -> Checker Sort'
        kSetW ks =
          if null ks
            then error $ "Cannot currently do a kind-level set"
            else
              error $ "Cannot currently do a kind-level set on kinds of sort " ++ pretty (head ks)

        kCase :: Sort' -> [(Sort', Sort')] -> Checker Sort'
        kCase wk wks =
          let k = unwrap wk
              ks = map (\(a, b) -> (unwrap a, unwrap b)) wks
          in kCaseW k ks

        kCaseW :: Type Two -> [(Type Two, Type Two)] -> Checker Sort'
        kCaseW k ks =
          -- Given that k, each pattern p and its corresponding branch b are well-kinded:
          -- The kind of k must be the same as the kind of each pattern p.
          if all (\x -> fst x == k) ks
            then -- All the branches must have the same kind.
              let bk = snd (head ks) in
                if all (\x -> snd x == bk) ks
                  then return $ W bk
                  -- Find the first branch that doesn't share a kind:
                  else
                    let (_, right) = partition (\x -> bk == snd x) ks in
                      throw $ SortMismatch { errLoc = s, kActualS = Nothing, sExpected = bk, sActual = snd (head right) }

            -- Find the first pattern that doesn't match the kind of k:
            else
              let (_, right) = partition (\x -> k == fst x) ks in
              throw $ SortMismatch { errLoc = s, kActualS = Nothing, sExpected = k, sActual = fst (head right) }

instance InferKind Zero where
  inferKindOfTypeInContext s quantifiedVariables t = do
      w <- typeFoldM0 (TypeFoldZero kFun kCon kBox kDiamond kVar kApp kInt kInfix kSet kCase) t
      return $ unwrap w
    where
      kFun :: Kind' -> Kind' -> Checker Kind'
      kFun (W (TyCon c)) (W (TyCon c'))
        | internalName c == internalName c' = return $ W $ TyCon c

      kFun (W (Type l)) (W (Type l')) | l == l' = return $ W $ Type l
      kFun (W (Type LZero)) (W (TyCon (internalName -> "Protocol"))) = return $ W $ TyCon (mkId "Protocol")
      kFun (W (Type l)) (W y) = throw KindMismatch{ errLoc = s, tyActualK = Nothing, kExpected = Type l, kActual = y }
      kFun (W x) _     = throw KindMismatch{ errLoc = s, tyActualK = Nothing, kExpected = Type LZero, kActual = x }

      kCon :: Id -> Checker Kind'
      kCon (internalName -> "Pure") = do
        -- Create a fresh type variable
        var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") (TyCon (mkId "Effect"))
        return $ W $ TyVar var
      kCon conId = do
          st <- get
          case lookup conId (typeConstructors st) of
              Just (TypeWithLevel (LSucc LZero) kind,_,_) -> return $ W kind
              _   -> do
                mConstructor <- lookupDataConstructor s conId
                case mConstructor of
                  Just (Forall _ [] [] t, _) -> do
                    k <- tryTyPromote s t
                    return $ W k
                  Just _ -> error $ pretty s <> "I'm afraid I can't yet promote the polymorphic data constructor:"  <> pretty conId
                  Nothing -> throw UnboundTypeConstructor{ errLoc = s, errId = conId }

      kBox :: Coeffect -> Kind' -> Checker Kind'
      kBox c (W (Type LZero)) = do
        -- Infer the coeffect (fails if that is ill typed)
        _ <- inferCoeffectType s c
        return $ W $ Type LZero
      kBox _ (W x) = throw KindMismatch{ errLoc = s, tyActualK = Nothing, kExpected = Type LZero, kActual = x }

      kDiamond :: Kind' -> Kind' -> Checker Kind'
      kDiamond (W effK) (W (Type LZero)) = do
        ef <- isEffectType s effK
        if ef
          then return $ W $ Type LZero
          else throw KindMismatch { errLoc = s, tyActualK = Just t, kExpected = (TyCon (mkId "Effect")), kActual = effK }

      kDiamond _ (W x)     = throw KindMismatch{ errLoc = s, tyActualK = Nothing, kExpected = Type LZero, kActual = x }

      kVar :: Id -> Checker Kind'
      kVar tyVar =
        case lookup tyVar quantifiedVariables of
          Just (TypeWithLevel (LSucc LZero) kind) -> return $ W kind
          _   -> do
            st <- get
            case lookup tyVar (tyVarContext st) of
              Just (TypeWithLevel (LSucc LZero) kind, _) -> return $ W kind
              _ -> throw UnboundTypeVariable{ errLoc = s, errId = tyVar }

      kApp :: Kind' -> Kind' -> Checker Kind'
      kApp (W (FunTy k1 k2)) (W kArg) = do
        kLub <- k1 `hasLub` kArg
        if kLub
          then return $ W k2
          else throw KindMismatch
                { errLoc = s
                , tyActualK = Nothing
                , kActual = kArg
                , kExpected = k1 }

      kApp (W k) (W kArg) = throw KindMismatch
          { errLoc = s
          , tyActualK = Nothing
          , kExpected = (FunTy kArg (TyVar $ mkId "..."))
          , kActual = k
          }

      kInt :: Int -> Checker Kind'
      kInt _ = return $ W $ TyCon $ mkId "Nat"

      kInfix :: TypeOperator -> Kind' -> Kind' -> Checker Kind'
      kInfix (tyOps -> (k1exp, k2exp, kret)) (W k1act) (W k2act) = do
        kLub <- k1act `hasLub` k1exp
        if not kLub
          then throw
            KindMismatch{ errLoc = s, tyActualK = Nothing, kExpected = k1exp, kActual = k1act}
          else do
            kLub' <- k2act `hasLub` k2exp
            if not kLub'
              then throw
                KindMismatch{ errLoc = s, tyActualK = Nothing, kExpected = k2exp, kActual = k2act}
              else pure $ W kret

      kSet :: [Kind'] -> Checker Kind'
      kSet wks = kSetW (map unwrap wks)

      kSetW :: [Kind] -> Checker Kind'
      kSetW ks =
        -- If the set is empty, then it could have any kind, so we need to make
        -- a kind which is `TyPromote (Set a)` for some type variable `a` of unknown kind
        if null ks
          then do
              -- create fresh polymorphic kind variable for this type
              vark <- freshIdentifierBase $ "set_elemk"
              -- remember this new kind variable in the kind environment
              modify (\st -> st { tyVarContext = (mkId vark, (TypeWithLevel (LSucc LZero) $ Type LZero, InstanceQ))
                                    : tyVarContext st })
              -- Create a fresh type variable
              var <- freshTyVarInContext (mkId $ "set_elem[" <> pretty (startPos s) <> "]") (TyVar $ mkId vark)
              k <- tryTyPromote s $ TyApp (TyCon $ mkId "Set") (TyVar var)
              return $ W k

          -- Otherwise, everything in the set has to have the same kind
          else
            if foldr (\x r -> (x == head ks) && r) True ks

              then  -- check if there is an alias (name) for sets of this kind
                  case lookup (head ks) setElements of
                      -- Lift this alias to the kind level
                      Just t -> do
                        k <- tryTyPromote s t
                        return $ W k
                      Nothing -> return $ W $ TyApp (TyCon $ mkId "Set") (head ks)
                      {-
                          -- Return a set type lifted to a kind
                          case demoteKindToType (head ks) of
                            Just t -> tryTyPromote s $ TyApp (TyCon $ mkId "Set") t
                            -- If the kind cannot be demoted then we shouldn't be making a set
                            Nothing -> throw $ KindCannotFormSet s (head ks)
                      -}

              -- Find the first occurence of a change in kind:
              else throw $ KindMismatch { errLoc = s , tyActualK = Nothing, kExpected = head left, kActual = head right }
                      where (left, right) = partition (\x -> (head ks) == x) ks

      kCase :: Kind' -> [(Kind', Kind')] -> Checker Kind'
      kCase wk wks =
        let k = unwrap wk
            ks = map (\(a, b) -> (unwrap a, unwrap b)) wks
        in kCaseW k ks

      kCaseW :: Kind -> [(Kind, Kind)] -> Checker Kind'
      kCaseW k ks =
        -- Given that k, each pattern p and its corresponding branch b are well-kinded:
        -- The kind of k must be the same as the kind of each pattern p.
        if all (\x -> fst x == k) ks
          then -- All the branches must have the same kind.
            let bk = snd (head ks) in
              if all (\x -> snd x == bk) ks
                then return $ W bk
                -- Find the first branch that doesn't share a kind:
                else
                  let (_, right) = partition (\x -> bk == snd x) ks in
                    throw $ KindMismatch { errLoc = s, tyActualK = Nothing, kExpected = bk, kActual = snd (head right) }

          -- Find the first pattern that doesn't match the kind of k:
          else
            let (_, right) = partition (\x -> k == fst x) ks in
            throw $ KindMismatch { errLoc = s, tyActualK = Nothing, kExpected = k, kActual = fst (head right) }

-- | Compute the join of two kinds, if it exists
joinKind :: (?globals :: Globals) => Kind -> Kind -> Checker (Maybe (Kind, Substitution))
joinKind k1 k2 | k1 == k2 = return $ Just (k1, [])
joinKind (TyVar v) k = return $ Just (k, [(v, SubstK k)])
joinKind k (TyVar v) = return $ Just (k, [(v, SubstK k)])
joinKind k1 k2 = do
  (coeffTy, _) <- mguCoeffectTypes nullSpan k1 k2
  --coeffTy <- tryTyPromote nullSpan coeffTy
  return $ Just (coeffTy, [])
--joinKind _ _ = return $ Nothing

joinSort :: Type Two -> Type Two -> Checker (Maybe (Type Two, Substitution))
joinSort s1 s2 | s1 == s2 = return $ Just (s1, [])
joinSort (TyVar v) s = return $ Just (s, [(v, SubstS s)])
joinSort s (TyVar v) = return $ Just (s, [(v, SubstS s)])
joinSort (KUnion s1 s2) s = do
  jS1 <- joinSort s s1
  case jS1 of
    Nothing -> do
        jS2 <- joinSort s s2
        case jS2 of
            Nothing -> return $ Nothing
            Just (s2', u) -> return $ Just (KUnion s1 s2', u)
    Just (s1', u) -> return $ Just (KUnion s1' s2, u)

joinSort s (KUnion s1 s2) = joinSort (KUnion s1 s2) s
joinSort _ _ = return $ Nothing

-- | Predicate on whether two kinds have a least upper bound
hasLub :: (?globals :: Globals) => Kind -> Kind -> Checker Bool
hasLub k1 k2 = do
  jK <- joinKind k1 k2
  case jK of
    Nothing -> return False
    Just _  -> return True

-- | Predicate on whether two sorts have a least upper bound
sHasLub :: Type Two -> Type Two -> Checker Bool
sHasLub s1 s2 = do
  jS <- joinSort s1 s2
  case jS of
    Nothing -> return False
    Just _  -> return True


-- | Infer the type of ta coeffect term (giving its span as well)
inferCoeffectType :: (?globals :: Globals) => Span -> Coeffect -> Checker (Type One)
inferCoeffectType s c = do
  st <- get
  inferCoeffectTypeInContext s (map (\(id, (k, _)) -> (id, k)) (tyVarContext st)) c

inferCoeffectTypeInContext :: (?globals :: Globals) => Span -> Ctxt TypeWithLevel -> Coeffect -> Checker (Type One)
-- Coeffect constants have an obvious kind
inferCoeffectTypeInContext _ _ (Level _)         = return $ TyCon $ mkId "Level"
inferCoeffectTypeInContext _ _ (CNat _)          = return $ TyCon $ mkId "Nat"
inferCoeffectTypeInContext _ _ (CFloat _)        = return $ TyCon $ mkId "Q"
inferCoeffectTypeInContext _ _ (CSet _)          = return $ TyCon $ mkId "Set"
inferCoeffectTypeInContext s ctxt (CProduct c1 c2)    = do
  k1 <- inferCoeffectTypeInContext s ctxt c1
  k2 <- inferCoeffectTypeInContext s ctxt c2
  return $ TyApp (TyApp (TyCon $ mkId "×") k1) k2

inferCoeffectTypeInContext s ctxt (CInterval c1 c2)    = do
  (k, _) <- mguCoeffectTypesFromCoeffects s c1 c2
  return $ TyApp (TyCon $ mkId "Interval") k

-- Take the join for compound coeffect epxressions
inferCoeffectTypeInContext s _ (CPlus c c')  = fmap fst $ mguCoeffectTypesFromCoeffects s c c'
inferCoeffectTypeInContext s _ (CMinus c c') = fmap fst $ mguCoeffectTypesFromCoeffects s c c'
inferCoeffectTypeInContext s _ (CTimes c c') = fmap fst $ mguCoeffectTypesFromCoeffects s c c'
inferCoeffectTypeInContext s _ (CMeet c c')  = fmap fst $ mguCoeffectTypesFromCoeffects s c c'
inferCoeffectTypeInContext s _ (CJoin c c')  = fmap fst $ mguCoeffectTypesFromCoeffects s c c'
inferCoeffectTypeInContext s _ (CExpon c c') = fmap fst $ mguCoeffectTypesFromCoeffects s c c'

-- Coeffect variables should have a type in the cvar->kind context
inferCoeffectTypeInContext s ctxt (CVar cvar) = do
  st <- get
  case lookup cvar ctxt of
    Nothing -> do
      throw UnboundTypeVariable{ errLoc = s, errId = cvar }
--      state <- get
--      let newType = TyVar $ "ck" <> show (uniqueVarId state)
      -- We don't know what it is yet though, so don't update the coeffect kind ctxt
--      put (state { uniqueVarId = uniqueVarId state + 1 })
--      return newType

    Just (TypeWithLevel (LSucc LZero) (TyVar   name)) -> return $ TyVar name
    --Just k -> checkKindIsCoeffect s ctxt k
    Just (TypeWithLevel (LSucc LZero) k) -> checkKindIsCoeffect s ctxt k
    --TODO: fix for cases where the universe level is wrong?
    Just _ -> throw UnboundTypeVariable{ errLoc = s, errId = cvar }

inferCoeffectTypeInContext s ctxt (CZero t) = checkKindIsCoeffect s ctxt t
inferCoeffectTypeInContext s ctxt (COne t)  = checkKindIsCoeffect s ctxt t
inferCoeffectTypeInContext s ctxt (CInfinity (Just t)) = checkKindIsCoeffect s ctxt t
-- Unknown infinity defaults to the interval of extended nats version
inferCoeffectTypeInContext s ctxt (CInfinity Nothing) = return (TyApp (TyCon $ mkId "Interval") extendedNat)
inferCoeffectTypeInContext s ctxt (CSig _ t) = checkKindIsCoeffect s ctxt t

inferCoeffectTypeAssumption :: (?globals :: Globals)
                            => Span -> Assumption -> Checker (Maybe (Type One))
inferCoeffectTypeAssumption _ (Linear _) = return Nothing
inferCoeffectTypeAssumption s (Discharged _ c) = do
    t <- inferCoeffectType s c
    return $ Just t

checkKindIsCoeffect :: (?globals :: Globals) => Span -> Ctxt TypeWithLevel -> Type One -> Checker (Type One)
checkKindIsCoeffect span ctxt ty = do
  kind <- inferKindOfTypeInContext span ctxt ty
  case kind of
    k | isCoeffectKind k -> return ty
    TyVar v ->
      case lookup v ctxt of
        Just (TypeWithLevel (LSucc (LSucc LZero)) k) | isCoeffectKind k -> return ty
        _ -> throw SortMismatch{ errLoc = span, kActualS = Just ty, sExpected = (TyCon (mkId "Coeffect")), sActual = kind }
    _ -> throw SortMismatch{ errLoc = span, kActualS = Just ty, sExpected = (TyCon (mkId "Coeffect")), sActual = kind }

-- Find the most general unifier of two coeffects
-- This is an effectful operation which can update the coeffect-kind
-- contexts if a unification resolves a variable
mguCoeffectTypesFromCoeffects :: (?globals :: Globals)
                 => Span -> Coeffect -> Coeffect -> Checker (Type One, (Coeffect -> Coeffect, Coeffect -> Coeffect))
mguCoeffectTypesFromCoeffects s c1 c2 = do
  coeffTy1 <- inferCoeffectType s c1
  coeffTy2 <- inferCoeffectType s c2
  mguCoeffectTypes s coeffTy1 coeffTy2

-- Given a type term, works out if its kind is actually an effect type (promoted)
-- if so, returns `Right effTy` where `effTy` is the effect type
-- otherwise, returns `Left k` where `k` is the kind of the original type term
isEffectType :: (?globals :: Globals) => Span -> Type One -> Checker Bool
isEffectType s ty = do
    kind <- inferKindOfType s ty
    return $ isEffectKind kind

-- Wrapper for TypeFold, since GHC has trouble deducing a ~ Type . Succ
data TypeSucc a = W { unwrap :: Type (Succ a) }
type Kind' = TypeSucc Zero
type Sort' = TypeSucc One