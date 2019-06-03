{- |
Module      :  Language.Granule.Checker.Interface.Check
Description :  Type-checking for interfaces and instances.

This module provides type-checking for interfaces and instances.
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}

{-# options_ghc -fno-warn-incomplete-uni-patterns #-}

module Language.Granule.Checker.Interface.Check
  (
  -- ** Context Solver
    solveIConstraints

  -- ** Interface Checking
  , checkIFaceHead
  , checkIFaceTys

  -- ** Instance Checking
  , checkInstHead
  , checkInstDefs

  -- ** Helpers
  , kindCheckSig
  , registerDefSig
  , substituteIConstraints
  ) where


import Control.Arrow (second)
import Control.Monad (unless)
import Control.Monad.State.Strict
import Data.List (groupBy, nub, union, (\\))
import Data.Maybe (catMaybes, fromMaybe)

import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Instance
import Language.Granule.Checker.Interface
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Types
import Language.Granule.Checker.Variables

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Helpers (freeVars)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Utils


-----------------
----- Types -----
-----------------


type Solver = Pred -> Span -> Id -> Checker (Maybe [CheckerError])


type CheckDef v = Span -> Id -> [Equation v ()] -> TypeScheme -> Checker (Def v Type)


--------------------------
----- Context Solver -----
--------------------------


solveIConstraints :: (?globals :: Globals) => Solver -> Substitution -> [Inst] -> Span -> TypeScheme -> Checker ()
solveIConstraints solver coercions itys sp tys = do
  itys' <- mapM (substitute coercions) itys
  topLevelExpanded <- mapM (substitute coercions) =<< getExpandedContext sp tys
  let remaining = itys' \\ topLevelExpanded
  mapM_ solveIConstraint remaining
    where solveIConstraint = verifyInstanceExists solver sp


------------------------------
----- Interface Checking -----
------------------------------


checkIFaceExists :: Span -> Id -> Checker ()
checkIFaceExists s n = requireInScope interfaceScope s n >> pure ()


checkIFaceHead :: (?globals :: Globals) => Interface -> Checker ()
checkIFaceHead iface@(Interface sp name constrs params itys) = do
  -- check that all of the variables used in the kinds are in scope
  let (pnames, pkinds) = unzip params'
      kindVars = freeVars pkinds
      remVars = kindVars \\ pnames
  mapM_ (unboundKindVariable sp) remVars
  let (_, icons) = partitionConstraints constrs
  withBindings params' ForallQ $ mapM_ (kindCheckConstraint sp) icons
  registerInterface sp name params' icons ifsigs
  where
    params' = fmap normaliseParameterKind params
    ifsigs = map (\(InterfaceMethod _ name tys) -> (name, tys)) itys


-- | Check an interface's method signatures.
checkIFaceTys :: (?globals :: Globals) => Interface -> Checker ()
checkIFaceTys iface@(Interface sp iname _ params itys) = do
  mapM_ (checkMethodSig iname (fmap normaliseParameterKind params)) itys


-- | Typecheck an interface method signature, and register it.
checkMethodSig :: (?globals :: Globals) => Id -> [(Id, Kind)] -> InterfaceMethod -> Checker ()
checkMethodSig iname params (InterfaceMethod sp name tys) = do
  let tys' = tysWithParams tys
  kindCheckSig sp tys'
  registerDefSig sp name tys'
  where
    -- | Inject the interface parameter and constraint into the
    -- | bindings and constraints of the typescheme.
    tysWithParams (Forall fsp binds constrs ty) =
        Forall fsp (binds <> params) (constrs <> [mkIFaceApp iname $ fmap fst params]) ty


-----------------------------
----- Instance Checking -----
-----------------------------


checkInstHead :: (?globals :: Globals) => Solver -> Instance v a -> Checker ()
checkInstHead solver (Instance sp iname constrs (InstanceTypes sp2 idty) _) = do
  initialTvc <- getTyVarContext

  let inst0 = mkInst iname idty
      instTy = tyFromInst inst0

  freeVarKinds <- getInstanceFreeVarKinds sp inst0
  (instTy', _, _, (preds, icons), _) <- freshPolymorphicInstance ForallQ False (Forall sp freeVarKinds constrs instTy) []

  let Just inst = fmap (mkInst iname . instParams) (instFromTy instTy')

  validateConstraint solver sp inst
  mapM_ (compileAndAddPredicate sp) preds

  subs <- mapM (kindCheckConstraint sp) icons
  _ <- either (conflictingKinds sp) pure =<< combineManySubstitutionsSafe sp subs

  -- we take it on faith that the instance methods are well-typed
  -- at this point. If an issue arises it will be caught before we
  -- check top-level definitions
  registerInstance sp inst
  putTyVarContext initialTvc
      where registerInstance :: (?globals :: Globals) => Span -> Inst -> Checker ()
            registerInstance sp inst = do
              maybeInstance <- getInstance solver sp inst
              case maybeInstance of
                Just (inst',_) ->
                    throw OverlappingInstance{ errLoc = sp, errInst1 = inst, errInst2 = inst' }
                Nothing -> do
                    maybeInstances <- lookupContext instanceContext iname
                    modify' $ \st -> st { instanceContext = (iname, (inst,constrs):fromMaybe [] maybeInstances)
                                                            : filter ((/=iname) . fst) (instanceContext st) }


checkInstDefs :: (?globals :: Globals) => CheckDef v -> Instance v () -> Checker (Instance v Type)
checkInstDefs checkDef (Instance sp iname constrs idat@(InstanceTypes _ idty) ds) = do
  let inst = mkInst iname idty

  (ifaceConstrs, methodSigs) <- instantiateInterface sp inst

  let (preds, constrs') = partitionConstraints constrs

  -- check that every instance method is a member of the interface
  names <- getInterfaceMembers sp iname
  defnames <- mapM (\(sp, name) ->
    checkInstDefName names sp name) [(sp, name) | (InstanceEquation sp (Just name) _) <- ds]

  -- check that an implementation is provided for every interface method
  forM_ (filter (`notElem` defnames) names)
    (\name -> throw MissingImplementation{ errLoc = sp, errId = name, errIFace = iname })

  -- group equations by method name
  let nameGroupedDefs = groupBy
        (\(InstanceEquation _ name1 _) (InstanceEquation _ name2 _) ->
          name1 == name2 || name2 == Nothing) ds
      groupedEqns = map
        (\((InstanceEquation sp (Just name) eq):dt) ->
          let eqs = map (\(InstanceEquation _ _ eq) -> eq) dt
          in ((sp, name), eq:eqs)) nameGroupedDefs

  -- check each implementation against the (normalised) method
  -- signature, and register the definition-form in the state
  let methods = [(sp, (name, tys, eqs)) | ((sp, name), eqs) <- groupedEqns,
                                          (name2, tys) <- methodSigs,
                                          name == name2]
  ds' <- mapM (\(sp, (name, tys, eqs)) -> do
                 tys' <- fmap (constrainTysWithPredicates preds) $ constrs' |> ifaceConstrs |> pure tys
                 registerInstanceSig iname idat name tys
                 checkDef sp name eqs tys') methods

  pure $ Instance sp iname constrs idat (concat $ fmap defToIDefs ds')
  where
    checkInstDefName names sp name = do
      unless (elem name names) (throw MethodNotMember{ errLoc = sp, errId = name, errIFace = iname })
      pure name
    defToIDefs (Def sp n eqns ty) = fmap (InstanceEquation sp (Just n)) eqns


---------------------
----- Utilities -----
---------------------


registerDefSig :: (?globals :: Globals) => Span -> Id -> TypeScheme -> Checker ()
registerDefSig sp name tys = do
  expanded <- expandIConstraints sp (iconsFromTys tys)
  registerExpandedConstraints sp name expanded
  modify' $ \st -> st { defContext = [(name, tys)] <> defContext st }


getInstance :: (?globals :: Globals) => Solver -> Span -> Inst -> Checker (Maybe (Inst, [Type]))
getInstance solver sp inst = do
  let iname = instIFace inst
  maybeInstances <- lookupContext instanceContext iname
  case maybeInstances of
    Nothing -> pure Nothing
    Just instances -> findM (unifiableWithInstance . fst) instances
    where
      findM :: (Monad m) => (a -> m Bool) -> [a] -> m (Maybe a)
      findM _ [] = pure Nothing
      findM f (x:xs) =
        f x >>= (\t -> if t then pure (Just x) else findM f xs)
      unifiableWithInstance :: Inst -> Checker Bool
      unifiableWithInstance ity =
          withInstanceContext sp ity $
            instancesAreEqual' solver sp ity inst


-- TODO: move this into Checker.Monad or Checker.Interface (these depend
--       on Checker.Substitutions, so there is a recursive import
--       - GuiltyDolphin (2019-02-22)
-- | Perform a substitution on the current interface constraint context.
substituteIConstraints :: (?globals :: Globals) => Substitution -> Checker ()
substituteIConstraints subst =
  getIConstraints >>= mapM (substitute subst) >>= putIcons


expandIConstraints :: (?globals :: Globals) => Span -> [Inst] -> Checker [Inst]
expandIConstraints sp icons = fmap (nub . concat) $ mapM expandIConstraint icons
  where expandIConstraint c = do
          parents <- getInterfaceDependenciesFlattened c
          pure (c : parents)
        getInterfaceDependenciesFlattened c = do
          parents <- getInterfaceConstraints' sp c
          parentsFlat <- fmap concat $ mapM getInterfaceDependenciesFlattened parents
          pure $ parents <> parentsFlat


-- | Retrieve the expanded interface context from the typescheme.
getExpandedContext :: (?globals :: Globals) => Span -> TypeScheme -> Checker [Inst]
getExpandedContext sp = expandIConstraints sp . iconsFromTys


verifyInstanceExists :: (?globals :: Globals) => Solver -> Span -> Inst -> Checker ()
verifyInstanceExists solver sp inst = do
  maybeInst <- getInstance solver sp inst
  case maybeInst of
    Nothing -> throw UnsatisfiedInstance{ errLoc = sp, errInst = inst }
    Just _ -> pure ()


getInterfaceConstraints' :: (?globals :: Globals) => Span -> Inst -> Checker [Inst]
getInterfaceConstraints' sp inst = do
  let iname = instIFace inst
      ipars = instParams inst
  params <- getInterfaceParameterNames sp iname
  constrs <- getInterfaceConstraints sp iname
  let subst = fmap (\(v,t) -> (v, SubstT t)) (zip params ipars)
  mapM (substitute subst) constrs


-- | Verify that the constraint is valid.
verifyConstraint :: (?globals :: Globals) => Solver -> Span -> Inst -> Checker ()
verifyConstraint solver sp cty = verifyInstanceExists solver sp cty


-- | Execute a checker with context from the instance head in scope.
withInstanceContext :: (?globals :: Globals) => Span -> Inst -> Checker a -> Checker a
withInstanceContext sp inst c = do
  tyVars <- getInstanceFreeVarKinds sp inst
  withBindings tyVars InstanceQ c


-- | Get the interface context of a typescheme.
iconsFromTys :: TypeScheme -> [Inst]
iconsFromTys (Forall _ _ constrs _) = constrsToIcons constrs


constrsToIcons :: [Type] -> [Inst]
constrsToIcons = catMaybes . fmap instFromTy


mkIFaceApp :: Id -> [Id] -> Type
mkIFaceApp iname = tyFromInst . mkInst iname . fmap TyVar


-- | Normalise the kind of the parameter, giving it a sensible
-- | default if no explicit kind signature is given.
normaliseParameterKind :: (Id, Maybe Kind) -> (Id, Kind)
normaliseParameterKind = second inferParameterKind
  where inferParameterKind = fromMaybe KType


getInstanceFreeVarKinds :: (?globals :: Globals) => Span -> Inst -> Checker [(Id, Kind)]
getInstanceFreeVarKinds sp inst = do
  kinds <- getInterfaceParameterKindsForInst sp inst
  getParamsFreeVarKinds sp (zip kinds (instParams inst))


-- | True if the two instances can be proven to be equal in the current context.
instancesAreEqual' :: (?globals :: Globals) => Solver -> Span -> Inst -> Inst -> Checker Bool
instancesAreEqual' solver sp t1 t2 = do
  res <- equalInstances sp t1 t2
  case res of
    Left{}   -> pure False
    Right pf -> do
      equalityPreds <- substitute (equalityProofSubstitution pf) (equalityProofConstraints pf)
      preds <- get >>= (substitute (equalityProofSubstitution pf) . predicateStack)
      let eqPred = Conj . fmap Con $ equalityPreds
          toSolve = Conj [Conj preds, eqPred]
      fmap (maybe True (const False)) $ solver toSolve sp (mkId "$internal")


unboundKindVariable :: Span -> Id -> Checker a
unboundKindVariable sp n =
  throw UnboundKindVariable{ errLoc = sp, errId = n }


------------------------------
----- Constraint Helpers -----
------------------------------


-- | Constrain the typescheme with the given constraint.
constrain :: (?globals :: Globals) => [Inst] -> TypeScheme -> Checker TypeScheme
constrain constrs (Forall sp binds constrs' ty) = do
  fvks <- fmap concat $ mapM (getInstanceFreeVarKinds sp) constrs
  pure $ Forall sp (union binds fvks) (fmap tyFromInst constrs <> constrs') ty


infixr 6 |>
(|>) :: (?globals :: Globals) => [Inst] -> Checker TypeScheme -> Checker TypeScheme
constrs |> tys = tys >>= constrain constrs


-- | Get the instantiated form of an interface at the point of a constraint.
-- |
-- | We require that both the interface and constraint are valid at the point
-- | of call.
instantiateInterface :: (?globals :: Globals) => Span -> Inst
                     -> Checker
                        ( [Inst]             -- ^ Instantiated constraints
                        , [(Id, TypeScheme)] -- ^ Instantiated method signatures
                        )
instantiateInterface sp inst = do
  let iname = instIFace inst
  sigs <- getInterfaceSigs sp iname
  subst <- getInstanceSubstitution sp inst
  constrs <- getInterfaceConstraints' sp inst

  -- instantiate method signatures with the constraint's parameters
  freeInstVarKinds <- getInstanceFreeVarKinds sp inst
  methodSigs <- mapM (\(name, sig) -> do
                        (Forall s binds constrs ty) <- withInterfaceContext sp iname $ substitute subst sig
                        -- ensure free variables in the instance head are universally quantified
                        pure (name, Forall s (binds <> freeInstVarKinds) constrs ty)) sigs
  pure (constrs, methodSigs)


-- | A possibly-failing operation that verifies a constraint is valid
-- | in the current context.
-- |
-- | The operation will fail if any of the following criteria are not met:
-- |
-- | - The constraint is not of a valid interface (i.e., the interface is not in scope)
-- | - The number of constraint parameters differs from the number of interface parameters
-- | - Any of the constraint parameters are not well-kinded with respect to the interface
-- |   parameters
-- | - Any of the interface's (instantiated) constraints are not satisfiable in the context
validateConstraint :: (?globals :: Globals) => Solver -> Span -> Inst -> Checker ()
validateConstraint solver sp inst = do
  let iname = instIFace inst

  -- verify that the associated interface is in scope
  checkIFaceExists sp iname

  -- make sure the number of parameters is correct
  let numParams = length (instParams inst)
  expectedNumParams <- fmap length (getInterfaceParameterNames sp iname)
  when (numParams /= expectedNumParams) $
    throw WrongNumberOfParameters{ errLoc = sp, errInst = inst
                                 , errParamNumExp = expectedNumParams
                                 , errParamNumAct = numParams }

  -- Make sure the constraint parameters are well-kinded
  -- with respect to the interface parameters (ensuring
  -- kind dependencies are resolved)
  _ <- withInstanceContext sp inst $ kindCheckConstraint sp inst

  -- Make sure all of the interface constraints are
  -- satisfiable in the context
  icons <- getInterfaceConstraints' sp inst
  mapM_ (verifyConstraint solver sp) icons


-- | Check that all the constraint parameters are well-kinded with respect
-- | to the interface, in the current context.
kindCheckConstraint :: (?globals :: Globals) => Span -> Inst -> Checker Substitution
kindCheckConstraint sp inst = do
  -- make sure we are dealing with an interface
  let iname = instIFace inst
  termKind <- getTerminalKind iname
  when (termKind /= KConstraint InterfaceC) $
    throw NotAnInterface{ errLoc = sp, errInst = inst }

  -- make sure the number of parameters is correct
  let numParams = length (instParams inst)
  expectedNumParams <- fmap length (getInterfaceParameterNames sp iname)
  when (numParams /= expectedNumParams) $
    throw WrongNumberOfParametersConstraint{ errLoc = sp, errInst = inst
                                 , errParamNumExp = expectedNumParams
                                 , errParamNumAct = numParams }

  -- check every parameter is well-kinded with respect to the interface
  kinds <- getInterfaceParameterKindsForInst sp inst
  let expectedKindPairs = zip (instParams inst) kinds
  subs <- forM expectedKindPairs (\(ity, iKind) -> do
    inferred <- inferKindOfTypeSafe sp ity
    case inferred of
      Left e -> throw e
      Right tyKind -> do
        eqres <- equalKinds sp iKind tyKind
        case eqres of
          Right pf -> pure $ equalityProofSubstitution pf
          Left{} -> throw KindMismatch{ errLoc = sp, kExpected = iKind, kActual = tyKind })
  sub <- combineManySubstitutionsSafe sp subs
  case sub of
    Left e -> conflictingKinds sp e
    Right sub -> pure sub
  where getTerminalKind = fmap terminalKind . getKindRequired sp
        terminalKind (KFun _ k) = terminalKind k
        terminalKind k = k


-- | Kind check a constraint in the current context.
-- |
-- | The constraint can be either a predicate, or an interface constraint.
kindCheckConstr :: (?globals :: Globals) => Span -> TConstraint -> Checker ()
kindCheckConstr s ty = do
  case instFromTy ty of
    -- interface constraint
    Just inst -> kindCheckConstraint s inst >> pure ()
    -- predicate
    Nothing -> do
      kind <- inferKindOfType s ty
      case kind of
        KConstraint Predicate -> pure ()
        _ -> throw KindMismatch{ errLoc = s, kExpected = KConstraint Predicate, kActual = kind }


-- | Kind-check a type scheme.
-- |
-- | We expect a type scheme to have kind 'KType'.
kindCheckSig :: (?globals :: Globals) => Span -> TypeScheme -> Checker ()
kindCheckSig s tys@(Forall _ quantifiedVariables constraints ty) = inTysContext $ do
  -- first, verify all the constraints are well-kinded
  mapM_ (kindCheckConstr s) constraints

  kind <- inferKindOfType s ty
  case kind of
    KType -> pure ()
    KPromote (TyCon k) | internalName k == "Protocol" -> pure ()
    _     -> throw KindMismatch{ errLoc = s, kExpected = KType, kActual = kind }
  where inTysContext = withBindings quantifiedVariables ForallQ


----------------------------
-- Type-inference Helpers --
----------------------------


-- | Given a set of (parameter kind, parameter type) pairs, attempt to
-- | map free variables in the types to appropriate kinds.
getParamsFreeVarKinds :: (?globals :: Globals) => Span -> [(Kind, Type)] -> Checker [(Id, Kind)]
getParamsFreeVarKinds sp = fmap (tyMapVars . snd) . getParamsKinds'
  where
    -- | Assigns a kind to each component of the type.
    getParamsKinds' :: [(Kind, Type)] -> Checker (Substitution, [(Type, Kind)])
    getParamsKinds' kts = do
      (subs, fvks) <- fmap unzip $ mapM (uncurry getParamKinds) kts
      sub <- either (conflictingKinds sp) pure =<< combineManySubstitutionsSafe sp subs
      fvks' <- instantiateKinds sub (concat fvks) >>= simplifyBindings
      pure (sub, fvks')
    getParamKinds :: Kind -> Type -> Checker (Substitution, [(Type, Kind)])
    getParamKinds paramKind (TyVar v) =
      pure ([(v, SubstK paramKind)], [(TyVar v, paramKind)])
    getParamKinds paramKind (Box c t) =
      getCoeffectFreeVarKinds c <*-> getParamKinds paramKind t
    getParamKinds paramKind t@(TyCoeffect (CVar v)) = pure ([], [(t, paramKind)])
    getParamKinds KType (FunTy f fArg) =
      let go = getParamKinds KType
      in go f <*-> go fArg
    getParamKinds paramKind t@TyApp{} =
      let go (TyApp c@(TyCon _) _) = pure c
          go (TyApp c@(TyVar _) _) = pure c
          go (TyApp n _) = go n
          go _ = Nothing
      in case go t of
           Just (TyCon n) -> do
             conKind <- getTyConKind sp n
             getParamsKinds' (getConArgKinds conKind t)
           -- when we have a variable, infer its kind from the parameters
           Just (TyVar v) -> do
             let fvs = freeVars (getArgs t)
             boundNames <- fmap (fmap fst) getTyVarContext
             argPolys <- mapM (\p -> do
                                 vk <- freshIdentifierBase "k"
                                 pure (p, KVar (mkId vk))) (getArgs t)
             varPolys <- mapM (\v -> do
                              vk <- freshIdentifierBase ("k_" <> internalName v)
                              pure (TyVar v, KVar (mkId vk))) ((fvs \\ boundNames) \\ (fmap fst $ tyMapVars argPolys))
             let polys = argPolys <> varPolys
             (sub, pks) <- let swap (x,y) = (y,x) in getParamsKinds' (fmap swap polys)
             paramKinds <- mapM (inferKindOfTypePoly polys) (getArgs t)
             let res = (TyVar v, foldKindsToDKind paramKind paramKinds) : pks
             pure (sub, res)
           _ -> pure ([], [(t, paramKind)])
    getParamKinds k (TyCoeffect c)
      | isBinaryCoeff c =
        let (n, m) = binaryCoeffComps c
            go = getParamKinds k . TyCoeffect
        in go n <*-> go m
    getParamKinds p@(KPromote (TyCon c)) t
      | internalName c == "Nat" =
        maybe (pure ([], [])) (getParamKinds p . TyCoeffect) (compileNatKindedTypeToCoeffectSafe t)
    getParamKinds (KPromote (TyApp (TyCon c) p)) (TyCoeffect (CInterval l u))
      | internalName c == "Interval" =
        let go = getParamKinds (KPromote p) . TyCoeffect in go l <*-> go u
    getParamKinds paramKind t = pure ([], [(t, paramKind)])

    -- | Get the kinds of coeffect variables in a coeffect.
    getCoeffectFreeVarKinds :: Coeffect -> Checker (Substitution, [(Type, Kind)])
    -- TODO: make sure this takes into account varying coeffect variables
    -- e.g., in "instance {NatCo n} => Simple (A [n]) where..."
    -- in which 'n' would have kind (KPromote (TyVar "Nat"))
    --     - GuiltyDolphin (2019-03-26)
    getCoeffectFreeVarKinds = pure . ([],) . (fmap (\v -> (TyCoeffect (CVar v), KCoeffect))) . freeVars

    getArgs :: Type -> [Type]
    getArgs = maybe [] snd . tyAppParts

    getArgKinds :: Kind -> [Kind]
    getArgKinds KType = []
    getArgKinds (KFun k kArg) = pure k <> getArgKinds kArg
    getArgKinds k = []

    -- | Fold a list of kind parameters into a KFun.
    -- |
    -- | The first argument is the result kind.
    foldKindsToDKind :: Kind -> [Kind] -> Kind
    foldKindsToDKind = foldr KFun

    getConArgKinds :: Kind -> Type -> [(Kind, Type)]
    getConArgKinds conKind conAp =
      let argKinds = getArgKinds conKind
          args     = getArgs conAp
      in zip argKinds args

    isBinaryCoeff CPlus{} = True
    isBinaryCoeff CTimes{} = True
    isBinaryCoeff CMinus{} = True
    isBinaryCoeff CMeet{} = True
    isBinaryCoeff CJoin{} = True
    isBinaryCoeff CExpon{} = True
    isBinaryCoeff _ = False

    binaryCoeffComps (CPlus x y) = (x, y)
    binaryCoeffComps (CTimes x y) = (x, y)
    binaryCoeffComps (CMinus x y) = (x, y)
    binaryCoeffComps (CJoin x y) = (x, y)
    binaryCoeffComps (CMeet x y) = (x, y)
    binaryCoeffComps (CExpon x y) = (x, y)
    binaryCoeffComps c = error $ "binaryCoeffComps called with: " <> show c

    zipKindVars :: Id -> Kind -> Kind -> Checker (Either FailedCombination Substitution)
    zipKindVars _ k (KVar v) = pure $ pure [(v, SubstK k)]
    zipKindVars v (KFun kf kArg) (KFun vf vArg) = do
      s1 <- zipKindVars v kf vf
      s2 <- zipKindVars v kArg vArg
      case (s1, s2) of
        (Right s1, Right s2) -> combineSubstitutionsSafe sp s1 s2
        (_, _) -> pure s1
    zipKindVars _ KType KType = pure $ pure mempty
    -- TODO: this seems a bit dodgy (having the substitution flipped),
    -- is this really what we want?
    --   - GuiltyDolphin (2019-04-02)
    zipKindVars v (KVar v') k = pure $ pure [(v', SubstK k)]
    zipKindVars _ (KPromote t) (KPromote t2) | t == t2 = pure $ pure mempty
    zipKindVars v k1 k2 = pure $ Left (v, SubstK k1, SubstK k2)

    instantiateKind :: (Id, Kind) -> [(Type, Kind)] -> Checker [(Type, Kind)]
    instantiateKind (v, k) kvs = do
      case lookup v (tyMapVars kvs) of
        Just k' -> do
          sub <- either (conflictingKinds sp) pure =<< zipKindVars v k k'
          mapM (\(n,k) -> fmap (n,) (substitute sub k)) kvs
        _ -> pure kvs

    tyMapVars :: [(Type, Kind)] -> [(Id, Kind)]
    tyMapVars [] = []
    tyMapVars ((TyVar v, k):xs) = (v, k) : tyMapVars xs
    tyMapVars (_:xs) = tyMapVars xs

    instantiateKinds sub vks = do
      foldM (\vks' (v, SubstK k) -> instantiateKind (v, k) vks') vks sub

    simplifyBindings = pure . nub

    inferKindOfTypePoly ret t =
      case lookup t ret of
        Nothing -> error $ "inferKindOfTypePoly called with: " <> prettyQuoted ret <> " and " <> prettyQuoted t
        Just k -> pure k

    infixl 4 <*->
    (<*->) :: (Semigroup a) => Checker (Substitution, a) -> Checker (Substitution, a) -> Checker (Substitution, a)
    (<*->) m n = do
      (sub1, r1) <- m
      (sub2, r2) <- n
      sub <- combineSubstitutionsSafe sp sub1 sub2
      case sub of
        Left e -> conflictingKinds sp e
        Right sub -> pure (sub, r1 <> r2)


conflictingKinds :: Span -> (Id, Substitutors, Substitutors) -> Checker a
conflictingKinds sp (v, k, k2) = throw
  ConflictingKinds{ errLoc = sp, errVar = v, errVal1 = k, errVal2 = k2 }
