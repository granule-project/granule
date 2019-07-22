-- Mainly provides a kind checker on types

module Language.Granule.Checker.Kinds (
                      inferKindOfType
                    , inferKindOfTypeInContext
                    , joinCoeffectTypes
                    , hasLub
                    , joinKind
                    , inferCoeffectType
                    , inferCoeffectTypeInContext
                    , inferCoeffectTypeAssumption
                    , mguCoeffectTypes
                    , promoteTypeToKind
                    , demoteKindToType
                    , isEffectType
                    , isEffectTypeFromKind
                    , isEffectKind
                    , isCoeffectKind) where

import Control.Monad.State.Strict

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

inferKindOfType :: (?globals :: Globals) => Span -> Type -> Checker Kind
inferKindOfType s t = do
    checkerState <- get
    inferKindOfTypeInContext s (stripQuantifiers $ tyVarContext checkerState) t

inferKindOfTypeInContext :: (?globals :: Globals) => Span -> Ctxt Kind -> Type -> Checker Kind
inferKindOfTypeInContext s quantifiedVariables t =
    typeFoldM (TypeFold kFun kCon kBox kDiamond kVar kApp kInt kInfix kSet) t
  where
    kFun (KPromote (TyCon c)) (KPromote (TyCon c'))
     | internalName c == internalName c' = return $ kConstr c

    kFun KType KType = return KType
    kFun KType (KPromote (TyCon (internalName -> "Protocol"))) = return $ KPromote (TyCon (mkId "Protocol"))
    kFun KType y = throw KindMismatch{ errLoc = s, tyActualK = Nothing, kExpected = KType, kActual = y }
    kFun x _     = throw KindMismatch{ errLoc = s, tyActualK = Nothing, kExpected = KType, kActual = x }

    kCon (internalName -> "Pure") = do
      -- Create a fresh type variable
      var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") KEffect
      return $ KPromote $ TyVar var
    kCon conId = do
        st <- get
        case lookup conId (typeConstructors st) of
            Just (kind,_) -> return kind
            Nothing   -> case lookup conId (dataConstructors st) of
                Just (Forall _ [] [] t, _) -> return $ KPromote t
                Just _ -> error $ pretty s <> "I'm afraid I can't yet promote the polymorphic data constructor:"  <> pretty conId
                Nothing -> throw UnboundTypeConstructor{ errLoc = s, errId = conId }

    kBox c KType = do
       -- Infer the coeffect (fails if that is ill typed)
       _ <- inferCoeffectType s c
       return KType
    kBox _ x = throw KindMismatch{ errLoc = s, tyActualK = Nothing, kExpected = KType, kActual = x }

    kDiamond effK KType = do
      effTyM <- isEffectTypeFromKind s effK
      case effTyM of
        Right effTy -> return KType
        Left otherk  -> throw KindMismatch { errLoc = s, tyActualK = Just t, kExpected = KEffect, kActual = otherk }

    kDiamond _ x     = throw KindMismatch{ errLoc = s, tyActualK = Nothing, kExpected = KType, kActual = x }

    kVar tyVar =
      case lookup tyVar quantifiedVariables of
        Just kind -> return kind
        Nothing   -> do
          st <- get
          case lookup tyVar (tyVarContext st) of
            Just (kind, _) -> return kind
            Nothing -> throw UnboundTypeVariable{ errLoc = s, errId = tyVar }

    kApp (KFun k1 k2) kArg | k1 `hasLub` kArg = return k2
    kApp k kArg = throw KindMismatch
        { errLoc = s
        , tyActualK = Nothing
        , kExpected = (KFun kArg (KVar $ mkId "..."))
        , kActual = k
        }

    kInt _ = return $ kConstr $ mkId "Nat"

    kInfix (tyOps -> (k1exp, k2exp, kret)) k1act k2act
      | not (k1act `hasLub` k1exp) = throw
        KindMismatch{ errLoc = s, tyActualK = Nothing, kExpected = k1exp, kActual = k1act}
      | not (k2act `hasLub` k2exp) = throw
        KindMismatch{ errLoc = s, tyActualK = Nothing, kExpected = k2exp, kActual = k2act}
      | otherwise                  = pure kret

    kSet ks =
      -- If the set is empty, then it could have any kind, so we need to make
      -- a kind which is `KPromote (Set a)` for some type variable `a` of unknown kind
      if null ks
        then do
            -- create fresh polymorphic kind variable for this type
            vark <- freshIdentifierBase $ "set_elemk"
            -- remember this new kind variable in the kind environment
            modify (\st -> st { tyVarContext = (mkId vark, (KType, InstanceQ))
                                   : tyVarContext st })
            -- Create a fresh type variable
            var <- freshTyVarInContext (mkId $ "set_elem[" <> pretty (startPos s) <> "]") (KPromote $ TyVar $ mkId vark)
            return $ KPromote $ TyApp (TyCon $ mkId "Set") (TyVar var)

        -- Otherwise, everything in the set has to have the same kind
        else
          if foldr (\x r -> (x == head ks) && r) True ks

            then  -- check if there is an alias (name) for sets of this kind
                case lookup (head ks) setElements of
                    -- Lift this alias to the kind level
                    Just t -> return $ KPromote t
                    Nothing ->
                        -- Return a set type lifted to a kind
                        case demoteKindToType (head ks) of
                           Just t -> return $ KPromote $ TyApp (TyCon $ mkId "Set") t
                           -- If the kind cannot be demoted then we shouldn't be making a set
                           Nothing -> throw $ KindCannotFormSet s (head ks)

            -- Find the first occurence of a change in kind:
            else throw $ KindMismatch { errLoc = s , tyActualK = Nothing, kExpected = head left, kActual = head right }
                    where (left, right) = partition (\x -> (head ks) == x) ks

-- | Compute the join of two kinds, if it exists
joinKind :: Kind -> Kind -> Maybe (Kind, Substitution)
joinKind k1 k2 | k1 == k2 = Just (k1, [])
joinKind (KVar v) k = Just (k, [(v, SubstK k)])
joinKind k (KVar v) = Just (k, [(v, SubstK k)])
joinKind (KPromote t1) (KPromote t2) =
   fmap (\k -> (KPromote k, [])) (joinCoeffectTypes t1 t2)

joinKind (KUnion k1 k2) k =
  case joinKind k k1 of
    Nothing ->
        case joinKind k k2 of
            Nothing -> Nothing
            Just (k2', u) -> Just (KUnion k1 k2', u)
    Just (k1', u) -> Just (KUnion k1' k2, u)

joinKind k (KUnion k1 k2) = joinKind (KUnion k1 k2) k

joinKind _ _ = Nothing

-- | Predicate on whether two kinds have a leasy upper bound
hasLub :: Kind -> Kind -> Bool
hasLub k1 k2 =
  case joinKind k1 k2 of
    Nothing -> False
    Just _  -> True

-- | Some coeffect types can be joined (have a least-upper bound). This
-- | function computes the join if it exists.
joinCoeffectTypes :: Type -> Type -> Maybe Type
joinCoeffectTypes t1 t2 = case (t1, t2) of
  -- Equal things unify to the same thing
  (t, t') | t == t' -> Just t

  -- `Nat` can unify with `Q` to `Q`
  (TyCon (internalName -> "Q"), TyCon (internalName -> "Nat")) ->
        Just $ TyCon $ mkId "Q"

  (TyCon (internalName -> "Nat"), TyCon (internalName -> "Q")) ->
        Just $ TyCon $ mkId "Q"

  -- `Nat` can unify with `Ext Nat` to `Ext Nat`
  (t, TyCon (internalName -> "Nat")) | t == extendedNat ->
        Just extendedNat
  (TyCon (internalName -> "Nat"), t) | t == extendedNat ->
        Just extendedNat

  (TyApp t1 t2, TyApp t1' t2') ->
    TyApp <$> joinCoeffectTypes t1 t1' <*> joinCoeffectTypes t2 t2'

  _ -> Nothing

-- | Infer the type of ta coeffect term (giving its span as well)
inferCoeffectType :: (?globals :: Globals) => Span -> Coeffect -> Checker Type
inferCoeffectType s c = do
  st <- get
  inferCoeffectTypeInContext s (map (\(id, (k, _)) -> (id, k)) (tyVarContext st)) c

inferCoeffectTypeInContext :: (?globals :: Globals) => Span -> Ctxt Kind -> Coeffect -> Checker Type
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
  k1 <- inferCoeffectTypeInContext s ctxt c1
  k2 <- inferCoeffectTypeInContext s ctxt c2

  case joinCoeffectTypes k1 k2 of
    Just k -> return $ TyApp (TyCon $ mkId "Interval") k

    Nothing -> throw IntervalGradeKindError{ errLoc = s, errTy1 = k1, errTy2 = k2 }

-- Take the join for compound coeffect epxressions
inferCoeffectTypeInContext s _ (CPlus c c')  = mguCoeffectTypes s c c'
inferCoeffectTypeInContext s _ (CMinus c c') = mguCoeffectTypes s c c'
inferCoeffectTypeInContext s _ (CTimes c c') = mguCoeffectTypes s c c'
inferCoeffectTypeInContext s _ (CMeet c c')  = mguCoeffectTypes s c c'
inferCoeffectTypeInContext s _ (CJoin c c')  = mguCoeffectTypes s c c'
inferCoeffectTypeInContext s _ (CExpon c c') = mguCoeffectTypes s c c'

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

    Just (KVar   name) -> return $ TyVar name
    Just (KPromote t)  -> checkKindIsCoeffect s ctxt t
    Just k             -> throw
      KindMismatch{ errLoc = s, tyActualK = Just $ TyVar cvar, kExpected = KPromote (TyVar $ mkId "coeffectType"), kActual = k }

inferCoeffectTypeInContext s ctxt (CZero t) = checkKindIsCoeffect s ctxt t
inferCoeffectTypeInContext s ctxt (COne t)  = checkKindIsCoeffect s ctxt t
inferCoeffectTypeInContext s ctxt (CInfinity (Just t)) = checkKindIsCoeffect s ctxt t
-- Unknown infinity defaults to the interval of extended nats version
inferCoeffectTypeInContext s ctxt (CInfinity Nothing) = return (TyApp (TyCon $ mkId "Interval") extendedNat)
inferCoeffectTypeInContext s ctxt (CSig _ t) = checkKindIsCoeffect s ctxt t

inferCoeffectTypeAssumption :: (?globals :: Globals)
                            => Span -> Assumption -> Checker (Maybe Type)
inferCoeffectTypeAssumption _ (Linear _) = return Nothing
inferCoeffectTypeAssumption s (Discharged _ c) = do
    t <- inferCoeffectType s c
    return $ Just t

checkKindIsCoeffect :: (?globals :: Globals) => Span -> Ctxt Kind -> Type -> Checker Type
checkKindIsCoeffect span ctxt ty = do
  kind <- inferKindOfTypeInContext span ctxt ty
  case kind of
    k | isCoeffectKind k -> return ty
    -- Came out as a promoted type, check that this is a coeffect
    KPromote k -> do
      kind' <- inferKindOfTypeInContext span ctxt k
      if isCoeffectKind kind'
        then return ty
        else throw KindMismatch{ errLoc = span, tyActualK = Just ty, kExpected = KCoeffect, kActual = kind }
    KVar v ->
      case lookup v ctxt of
        Just k | isCoeffectKind k -> return ty
        _              -> throw KindMismatch{ errLoc = span, tyActualK = Just ty, kExpected = KCoeffect, kActual = kind }

    _ -> throw KindMismatch{ errLoc = span, tyActualK = Just ty, kExpected = KCoeffect, kActual = kind }

-- Find the most general unifier of two coeffects
-- This is an effectful operation which can update the coeffect-kind
-- contexts if a unification resolves a variable
mguCoeffectTypes :: (?globals :: Globals) => Span -> Coeffect -> Coeffect -> Checker Type
mguCoeffectTypes s c1 c2 = do
  ck1 <- inferCoeffectType s c1
  ck2 <- inferCoeffectType s c2
  case (ck1, ck2) of
    -- Both are variables
    (TyVar kv1, TyVar kv2) | kv1 /= kv2 -> do
      updateCoeffectType kv1 (KVar kv2)
      return (TyVar kv2)

    (t, t') | t == t' -> return t

   -- Linear-hand side is a poly variable, but right is concrete
    (TyVar kv1, ck2') -> do
      updateCoeffectType kv1 (promoteTypeToKind ck2')
      return ck2'

    -- Right-hand side is a poly variable, but Linear is concrete
    (ck1', TyVar kv2) -> do
      updateCoeffectType kv2 (promoteTypeToKind ck1')
      return ck1'

    (TyCon k1, TyCon k2) | k1 == k2 -> return $ TyCon k1

    -- Try to unify coeffect types
    (t, t') | Just tj <- joinCoeffectTypes t t' -> return tj

    -- Unifying a product of (t, t') with t yields (t, t') [and the symmetric version]
    (isProduct -> Just (t1, t2), t) | t1 == t -> return $ ck1
    (isProduct -> Just (t1, t2), t) | t2 == t -> return $ ck1
    (t, isProduct -> Just (t1, t2)) | t1 == t -> return $ ck2
    (t, isProduct -> Just (t1, t2)) | t2 == t -> return $ ck2

    (k1, k2) -> throw CoeffectUnificationError
      { errLoc = s, errTy1 = k1, errTy2 = k2, errC1 = c1, errC2 = c2 }

-- Given a coeffect type variable and a coeffect kind,
-- replace any occurence of that variable in a context
updateCoeffectType :: Id -> Kind -> Checker ()
updateCoeffectType tyVar k = do
   modify (\checkerState ->
    checkerState
     { tyVarContext = rewriteCtxt (tyVarContext checkerState) })
 where
   rewriteCtxt :: Ctxt (Kind, Quantifier) -> Ctxt (Kind, Quantifier)
   rewriteCtxt [] = []
   rewriteCtxt ((name, (KPromote (TyVar kindVar), q)) : ctxt)
    | tyVar == kindVar = (name, (k, q)) : rewriteCtxt ctxt
   rewriteCtxt ((name, (KVar kindVar, q)) : ctxt)
    | tyVar == kindVar = (name, (k, q)) : rewriteCtxt ctxt
   rewriteCtxt (x : ctxt) = x : rewriteCtxt ctxt

-- Given a type term, works out if its kind is actually an effect type (promoted)
-- if so, returns `Right effTy` where `effTy` is the effect type
-- otherwise, returns `Left k` where `k` is the kind of the original type term
isEffectType :: (?globals :: Globals) => Span -> Type -> Checker (Either Kind Type)
isEffectType s ty = do
    kind <- inferKindOfType s ty
    isEffectTypeFromKind s kind

isEffectTypeFromKind :: (?globals :: Globals) => Span -> Kind -> Checker (Either Kind Type)
isEffectTypeFromKind s kind =
    case kind of
        KPromote effTy -> do
            kind' <- inferKindOfType s effTy
            if isEffectKind kind'
                then return $ Right effTy
                else return $ Left kind
        _ -> return $ Left kind

isEffectKind :: Kind -> Bool
isEffectKind KEffect = True
isEffectKind (KUnion _ KEffect) = True
isEffectKind (KUnion KEffect _) = True
isEffectKind _ = False

isCoeffectKind :: Kind -> Bool
isCoeffectKind KCoeffect = True
isCoeffectKind (KUnion _ KCoeffect) = True
isCoeffectKind (KUnion KCoeffect _) = True
isCoeffectKind _ = False