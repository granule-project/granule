
module Language.Granule.Checker.KindsImplicit where

import Control.Monad.State.Strict

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Primitives (tyOps)
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Variables

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Context
import Language.Granule.Utils

-- | Check the kind of a definition
-- Currently we expect that a type scheme has kind KType
kindCheckDef :: (?globals :: Globals) => Def v t -> Checker (Def v t)
kindCheckDef (Def s id eqs (Forall s' quantifiedVariables constraints ty)) = do
  -- Set up the quantified variables in the type variable context
  modify (\st -> st { tyVarContext = map (\(n, c) -> (n, (c, ForallQ))) quantifiedVariables})

  forM_ constraints $ \constraint -> do
    (kind, _) <- inferKindOfTypeImplicits s quantifiedVariables constraint
    case kind of
      KPredicate -> return ()
      _ -> throw KindMismatch{ errLoc = s, tyActualK = Just constraint, kExpected = KPredicate, kActual = kind }

  (kind, unifiers) <- inferKindOfTypeImplicits s quantifiedVariables ty
  case kind of
    KType -> do
        -- Rewrite the quantified variables with their possibly updated kinds (inferred)
        qVars <- mapM (\(v, a) -> substitute unifiers a >>= (\b -> return (v, b)))
                   quantifiedVariables
        modify (\st -> st { tyVarContext = [] })
        -- Update the def with the resolved quantifications
        return (Def s id eqs (Forall s' qVars constraints ty))

    --KPromote (TyCon k) | internalName k == "Protocol" -> modify (\st -> st { tyVarContext = [] })
    _     -> throw KindMismatch{ errLoc = s, tyActualK = Just ty, kExpected = KType, kActual = kind }

kindIsKind :: Kind -> Bool
kindIsKind (KPromote (TyCon (internalName -> "Kind"))) = True
kindIsKind _ = False

-- Infers the kind of a type, but also allows some of the type variables to have poly kinds
-- which get automatically resolved
inferKindOfTypeImplicits :: (?globals :: Globals) => Span -> Ctxt Kind -> Type -> Checker (Kind, Substitution)

inferKindOfTypeImplicits s ctxt (FunTy t1 t2) = do
   (k1, u1) <- inferKindOfTypeImplicits s ctxt t1
   (k2, u2) <- inferKindOfTypeImplicits s ctxt t2
   case joinKind k1 KType of
    Just (k1, u1') ->
      case joinKind k2 KType of
        Just (k2, u2') -> do
          u <- combineManySubstitutions s [u1, u2, u1', u2']
          return (KType, u)
        _ -> throw KindMismatch{ errLoc = s, tyActualK = Just t2, kExpected = KType, kActual = k2 }
    _ -> throw KindMismatch{ errLoc = s, tyActualK = Just t1, kExpected = KType, kActual = k2 }

-- kFun KType (KPromote (TyCon (internalName -> "Protocol"))) = return $ KPromote (TyCon (mkId "Protocol"))

inferKindOfTypeImplicits s ctxt (TyCon (internalName -> "Pure")) = do
    -- Create a fresh type variable
    var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") KEffect
    return $ (KPromote $ TyVar var, [])

inferKindOfTypeImplicits s ctxt (TyCon conId) = do
  st <- get
  case lookup conId (typeConstructors st) of
    Just (kind,_) -> return (kind, [])
    Nothing   -> case lookup conId (dataConstructors st) of
      Just (Forall _ [] [] t, _) -> return (KPromote t, [])
      Just _ -> error $ pretty s <> "I'm afraid I can't yet promote the polymorphic data constructor:"  <> pretty conId
      Nothing -> throw UnboundTypeConstructor{ errLoc = s, errId = conId }

inferKindOfTypeImplicits s ctxt (Box c t) = do
    _ <- inferCoeffectTypeInContext s ctxt c
    (k, u) <- inferKindOfTypeImplicits s ctxt t
    case joinKind k KType of
      Just (k, u') -> do
        u'' <- combineSubstitutions s u u'
        return (KType, u'')
      _ -> throw KindMismatch{ errLoc = s, tyActualK = Just t, kExpected = KType, kActual = k }

inferKindOfTypeImplicits s ctxt (Diamond e t) = do
  (ke, u') <- inferKindOfTypeImplicits s ctxt e
  liftIO $ putStrLn $ " ke = " <> pretty ke <> " e = " <> pretty e
  (k, u) <- inferKindOfTypeImplicits s ctxt t
  case joinKind k KType of
    Just (k, u2) -> do
      case ke of
        KPromote effTy -> do
            (effTyK, u3) <- inferKindOfTypeImplicits s ctxt effTy
            liftIO $ putStrLn $ "effTyK = " <> pretty effTyK <> " effTy " <> pretty effTy
            case joinKind effTyK KEffect of
              Just (_, u4) -> do
                u5 <- combineManySubstitutions s [u, u', u2, u3, u4]
                return (KType, u5)
              _ -> throw KindMismatch { errLoc = s, tyActualK = Just effTy, kExpected = KEffect, kActual = effTyK }
        -- TODO: create a custom error message for this
        otherk  -> throw KindMismatch { errLoc = s, tyActualK = Just e, kExpected = KPromote (TyVar $ mkId "effectType"), kActual = otherk }
    _ -> throw KindMismatch{ errLoc = s, tyActualK = Just t, kExpected = KType, kActual = k }

inferKindOfTypeImplicits s ctxt (TyVar tyVar) =
  case lookup tyVar ctxt of
    Just kind -> return (kind, [])
    Nothing   -> do
      st <- get
      case lookup tyVar (tyVarContext st) of
        Just (kind, _) -> return (kind, [])
        Nothing ->
          throw UnboundTypeVariable{ errLoc = s, errId = tyVar }

inferKindOfTypeImplicits s ctxt (TyApp t1 t2) = do
  (k1, u1) <- inferKindOfTypeImplicits s ctxt t1
  case k1 of
    KFun k1 k2 -> do
      (kArg, u2) <- inferKindOfTypeImplicits s ctxt t2
      case (joinKind k1 kArg) of
        Just (k, uk) -> do
          u <- combineManySubstitutions s [u1, u2, uk]
          k2' <- substitute u k2
          return (k2', u)
        Nothing -> throw KindMismatch{ errLoc = s, tyActualK = Just t2, kExpected = k1, kActual = kArg }
    KVar v -> do
        (kArg, u2) <- inferKindOfTypeImplicits s ctxt t2
        kResVar <- freshIdentifierBase $ "_kres"
        let u = [(v, SubstK $ KFun (KVar $ mkId kResVar) kArg)]
        uOut <- combineSubstitutions s u2 u
        return (KVar $ mkId kResVar, uOut)

    _ -> throw KindMismatch{ errLoc = s, tyActualK = Just t1, kExpected = KFun (KVar $ mkId "..") (KVar $ mkId ".."), kActual = k1 }

inferKindOfTypeImplicits s ctxt (TyInt _) = return $ (kConstr $ mkId "Nat", [])

inferKindOfTypeImplicits s ctxt (TyInfix (tyOps -> (k1exp, k2exp, kret)) t1 t2) = do
  (k1act, u1) <- inferKindOfTypeImplicits s ctxt t1
  (k2act, u2) <- inferKindOfTypeImplicits s ctxt t2
  case joinKind k1act k1exp of
    Just (k1, u3) ->
      case joinKind k2act k2exp of
        Just (k2, u4) -> do
          u <- combineManySubstitutions s [u1, u2, u3, u4]
          kret' <- substitute u kret
          return (kret', u)

        Nothing -> throw KindMismatch{ errLoc = s, tyActualK = Just t2, kExpected = k2exp, kActual = k2act}
    Nothing -> throw KindMismatch{ errLoc = s, tyActualK = Just t1, kExpected = k1exp, kActual = k1act}

-- Fall back to regular kind infererence for now
inferKindOfTypeImplicits s ctxt (TySet ts) = do
    -- ks <- mapM (inferKindOfTypeImplicits s ctxt) ts
    k <- inferKindOfTypeInContext s ctxt (TySet ts)
    return (k, [])