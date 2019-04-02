{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Checker where

import Control.Arrow (second)
import Control.Monad (unless)
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Data.List (genericLength, groupBy, intercalate, nub, (\\))
import Data.Maybe
import qualified Data.Text as T

import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Errors
import Language.Granule.Checker.Coeffects
import Language.Granule.Checker.Constraints
import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Exhaustivity
import Language.Granule.Checker.Instance
import Language.Granule.Checker.Interface
  ( getInterfaceSigs
  , getInterfaceMembers
  , getInterfaceParameterNames
  , getInterfaceConstraints
  , registerInstanceSig
  , withInterfaceContext
  )
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Patterns
import Language.Granule.Checker.Predicates
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Checker.Rewrite.Type (RewriteEnv)
import Language.Granule.Checker.Simplifier
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.Types
import Language.Granule.Checker.Variables
import Language.Granule.Context

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Helpers (freeVars)
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Utils

--import Debug.Trace

-- Checking (top-level)
check :: (?globals :: Globals, Pretty v) => AST v () -> IO (Maybe (RewriteEnv, (AST v Type)))
check (AST dataDecls defs ifaces insts) = evalChecker initState $ do
    rs1 <- mapM (runMaybeT . checkTyCon) dataDecls
    rs2 <- mapM (runMaybeT . checkDataCons) dataDecls
    rsIFHeads <- mapM (runMaybeT . checkIFaceHead) ifaces
    rsIFTys <- mapM (runMaybeT . checkIFaceTys) ifaces
    rsInstHeads <- mapM (runMaybeT . checkInstHead) insts
    rs3 <- mapM (runMaybeT . checkDefTy) defs
    rsInstDefs <- mapM (runMaybeT . checkInstDefs) insts
    rs4 <- mapM (runMaybeT . checkDef) defs

    renv <- fmap checkerStateToRewriterEnv get

    pure $
      if all isJust (rs1 <> rs2
                     <> rsIFHeads
                     <> rsIFTys
                     <> rsInstHeads
                     <> forgetRes rsInstDefs
                     <> rs3 <> forgetRes rs4)
        then Just (renv, AST dataDecls (catMaybes rs4) ifaces (catMaybes rsInstDefs))
        else Nothing
    where forgetRes = fmap (fmap (const ()))


checkTyCon :: (?globals :: Globals) => DataDecl -> MaybeT Checker ()
checkTyCon (DataDecl sp name tyVars kindAnn ds) = do
  registerTyCon sp name tyConKind cardin
  where
    cardin = (Just . genericLength) ds -- the number of data constructors
    tyConKind = mkKind (map snd tyVars)
    mkKind [] = case kindAnn of Just k -> k; Nothing -> KType -- default to `Type`
    mkKind (v:vs) = KFun v (mkKind vs)

checkDataCons :: (?globals :: Globals) => DataDecl -> MaybeT Checker ()
checkDataCons (DataDecl _ name tyVars _ dataConstrs) =
     do
    st <- get
    let Just (kind,_) = lookup name (typeConstructors st) -- can't fail, tyCon must be in checker state
    modify' $ \st -> st { tyVarContext = [(v, (k, ForallQ)) | (v, k) <- tyVars] }
    mapM_ (checkDataCon name kind tyVars) dataConstrs

checkDataCon :: (?globals :: Globals)
  => Id -- ^ The type constructor and associated type to check against
  -> Kind -- ^ The kind of the type constructor
  -> Ctxt Kind -- ^ The type variables
  -> DataConstr -- ^ The data constructor to check
  -> MaybeT Checker () -- ^ Return @Just ()@ on success, @Nothing@ on failure
checkDataCon tName kind tyVarsT (DataConstrIndexed sp dName tySch@(Forall s tyVarsD constraints ty)) =
    case intersectCtxts tyVarsT tyVarsD of
      [] -> do -- no clashes

        -- Only relevant type variables get included
        let tyVars = relevantSubCtxt (freeVars ty) (tyVarsT <> tyVarsD)
        let tyVars_justD = relevantSubCtxt (freeVars ty) tyVarsD

        -- Add the type variables from the data constructor into the environment
        modify $ \st -> st { tyVarContext =
               [(v, (k, ForallQ)) | (v, k) <- tyVars_justD] ++ tyVarContext st }
        tySchKind <- inferKindOfType' sp tyVars ty

        -- Freshen the data type constructors type
        (ty, tyVarsFreshD, _, (predConstrs, iConstrs), []) <-
             freshPolymorphicInstance ForallQ False (Forall s tyVars constraints ty) []

        -- Create a version of the data constructor that matches the data type head
        -- but with a list of coercions

        (ty', coercions, tyVarsNewAndOld) <- checkAndGenerateSubstitution sp tName ty (indexKinds kind)

        -- Reconstruct the data constructor's new type scheme
        let tyVarsD' = tyVarsFreshD <> tyVarsNewAndOld
        let tySch = Forall sp tyVarsD' (predConstrs <> constrsFromIcons iConstrs) ty'

        case tySchKind of
          KType ->
            registerDataConstructor tySch coercions

          KPromote (TyCon k) | internalName k == "Protocol" ->
            registerDataConstructor tySch coercions

          _     -> illKindedNEq sp KType kind

      vs -> halt $ NameClashError (Just sp) $ mconcat
                    ["Type variable(s) ", intercalate ", " $ map (\(i,_) -> "`" <> pretty i <> "`") vs
                    ," in data constructor `", pretty dName
                    ,"` are already bound by the associated type constructor `", pretty tName
                    , "`. Choose different, unbound names."]
  where
    indexKinds (KFun k1 k2) = k1 : indexKinds k2
    indexKinds k = []

    registerDataConstructor dataConstrTy subst = do
      st <- get
      case extend (dataConstructors st) dName (dataConstrTy, subst) of
        Some ds -> do
          put st { dataConstructors = ds, tyVarContext = [] }
        None _ -> halt $ NameClashError (Just sp) $ "Data constructor `" <> pretty dName <> "` already defined."

checkDataCon tName kind tyVars d@DataConstrNonIndexed{}
  = checkDataCon tName kind tyVars
    $ nonIndexedToIndexedDataConstr tName tyVars d


{-
    Checks whether the type constructor name matches the return constraint
    of the data constructor
    and at the same time generate coercions for every parameter of result type type constructor
    then generate fresh variables for parameter and coercions that are either trivial
    variable ones or to concrete types

    e.g.
      checkAndGenerateSubstitution Maybe (a' -> Maybe a') [Type]
      > (a' -> Maybe a, [a |-> a'], [a : Type])

      checkAndGenerateSubstitution Other (a' -> Maybe a') [Type]
      > *** fails

      checkAndGenerateSubstitution Vec (Vec 0 t') [Nat, Type]
      > (Vec n t', [n |-> Subst 0, t |-> t'], [n : Type, ])

      checkAndGenerateSubstitution Vec (t' -> Vec n' t' -> Vec (n'+1) t') [Nat, Type]
      > (t' -> Vec n' t' -> Vec n t, [n |-> Subst (n'+1), t |-> t'], [])

      checkAndGenerateSubstitution Foo (Int -> Foo Int) [Type]
      > (Int -> Foo t1, [t1 |-> Subst Int], [t1 : Type])

-}

checkAndGenerateSubstitution ::
       (?globals :: Globals)
    => Span                     -- ^ Location of this application
    -> Id                       -- ^ Name of the type constructor
    -> Type                     -- ^ Type of the data constructor
    -> [Kind]                   -- ^ Types of the remaining data type indices
    -> MaybeT Checker (Type, Substitution, Ctxt Kind)
checkAndGenerateSubstitution sp tName ty ixkinds =
    checkAndGenerateSubstitution' sp tName ty (reverse ixkinds)

checkAndGenerateSubstitution' sp tName (TyCon tC) [] =
    -- Check the name
    if tC == tName
      then return (TyCon tC, [], [])
      else halt $ GenericError (Just sp)
                $ "Expected type constructor `" <> pretty tName
               <> "`, but got `" <> pretty tC <> "`"

checkAndGenerateSubstitution' sp tName (FunTy arg res) kinds = do
   (res', subst, tyVarsNew) <- checkAndGenerateSubstitution' sp tName res kinds
   return (FunTy arg res', subst, tyVarsNew)

checkAndGenerateSubstitution' sp tName (TyApp fun arg) (kind:kinds) = do
  varSymb <- freshIdentifierBase "t"
  let var = mkId varSymb
  (fun', subst, tyVarsNew) <-  checkAndGenerateSubstitution' sp tName fun kinds
  return (TyApp fun' (TyVar var), (var, SubstT arg) : subst, (var, kind) : tyVarsNew)

checkAndGenerateSubstitution' sp _ x _ =
  halt $ GenericError (Just sp) $ "`" <> pretty x <> "` not valid in a datatype definition."


checkIFaceExists :: (?globals :: Globals) => Span -> Id -> MaybeT Checker ()
checkIFaceExists s = void . requireInScope (ifaceContext, "Interface") s


checkIFaceHead :: (?globals :: Globals) => Interface -> MaybeT Checker ()
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


registerDefSig :: (?globals :: Globals) => Span -> Id -> TypeScheme -> MaybeT Checker ()
registerDefSig sp name tys = do
  checkDuplicate (defContext, "Definition") sp name
  expanded <- expandIConstraints sp (iconsFromTys tys)
  registerExpandedConstraints sp name expanded
  modify' $ \st -> st { defContext = [(name, tys)] <> defContext st }


-- | Check an interface's method signatures.
checkIFaceTys :: (?globals :: Globals) => Interface -> MaybeT Checker ()
checkIFaceTys iface@(Interface sp iname _ params itys) = do
  mapM_ (checkMethodSig iname (fmap normaliseParameterKind params)) itys


-- | Typecheck an interface method signature, and register it.
checkMethodSig :: (?globals :: Globals) => Id -> [(Id, Kind)] -> InterfaceMethod -> MaybeT Checker ()
checkMethodSig iname params (InterfaceMethod sp name tys) = do
  let tys' = tysWithParams tys
  kindCheckSig sp tys'
  registerDefSig sp name tys'
  where
    -- | Inject the interface parameter and constraint into the
    -- | bindings and constraints of the typescheme.
    tysWithParams (Forall fsp binds constrs ty) =
        Forall fsp (binds <> params) (constrs <> [mkIFaceApp iname $ fmap fst params]) ty


getInstance :: (?globals :: Globals) => Span -> Inst -> MaybeT Checker (Maybe (Inst, [Type]))
getInstance sp inst = do
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
      unifiableWithInstance :: Inst -> MaybeT Checker Bool
      unifiableWithInstance ity =
          withInstanceContext sp ity $
            instancesAreEqual' sp inst ity


checkInstHead :: (?globals :: Globals) => Instance v a -> MaybeT Checker ()
checkInstHead (Instance sp iname constrs (InstanceTypes sp2 idty) _) = do
  initialTvc <- getTyVarContext

  let inst0 = mkInst iname idty
      instTy = tyFromInst inst0

  freeVarKinds <- getInstanceFreeVarKinds sp inst0
  (instTy', _, _, (preds, icons), _) <- freshPolymorphicInstance ForallQ False (Forall sp freeVarKinds constrs instTy) []

  let Just inst = fmap (mkInst iname . instParams) (instFromTy instTy')

  validateConstraint sp inst
  mapM_ (compileAndAddPredicate sp) preds

  subs <- mapM (kindCheckConstraint sp) icons
  either (conflictingKinds sp) pure =<< combineManySubstitutionsSafe sp subs

  -- we take it on faith that the instance methods are well-typed
  -- at this point. If an issue arises it will be caught before we
  -- check top-level definitions
  registerInstance sp inst
  putTyVarContext initialTvc
      where registerInstance :: (?globals :: Globals) => Span -> Inst -> MaybeT Checker ()
            registerInstance sp inst = do
              maybeInstance <- getInstance sp inst
              case maybeInstance of
                Just (inst',_) ->
                    halt . NameClashError (Just sp) $
                      concat [ "The instance ", prettyQuoted inst
                             , " overlaps with the previously defined instance "
                             , prettyQuoted inst' ]
                Nothing -> do
                    maybeInstances <- lookupContext instanceContext iname
                    modify' $ \st -> st { instanceContext = (iname, (inst,constrs):fromMaybe [] maybeInstances)
                                                            : filter ((/=iname) . fst) (instanceContext st) }


checkInstDefs :: (?globals :: Globals, Pretty v) => Instance v () -> MaybeT Checker (Instance v Type)
checkInstDefs (Instance sp iname constrs idat@(InstanceTypes _ idty) ds) = do
  let inst = mkInst iname idty

  (ifaceConstrs, methodSigs) <- instantiateInterface sp inst

  let (preds, constrs') = partitionConstraints constrs

  -- check that every instance method is a member of the interface
  names <- getInterfaceMembers sp iname
  defnames <- mapM (\(sp, name) ->
    checkInstDefName names sp name) [(sp, name) | (InstanceEquation sp (Just name) _) <- ds]

  -- check that an implementation is provided for every interface method
  forM_ (filter (`notElem` defnames) names)
    (\name -> halt $ GenericError (Just sp) $
      concat ["No implementation given for `", pretty name
             , "` which is a required member of interface `"
             , pretty iname, "`"])

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
                 checkDef' sp name eqs tys') methods

  pure $ Instance sp iname constrs idat (concat $ fmap defToIDefs ds')
  where
    checkInstDefName names sp name = do
      unless (elem name names) (halt $ GenericError (Just sp) $
        concat ["`", pretty name, "` is not a member of interface `", pretty iname, "`"])
      pure name
    defToIDefs (Def sp n eqns ty) = fmap (InstanceEquation sp (Just n)) eqns


checkDefTy :: (?globals :: Globals) => Def v a -> MaybeT Checker ()
checkDefTy d@(Def sp name _ tys) = do
  kindCheckSig sp tys
  registerDefSig sp name tys


checkDef' :: (?globals :: Globals, Pretty v)
         => Span -> Id -> [Equation v ()]
         -> TypeScheme
         -> MaybeT Checker (Def v Type)
checkDef' s defName equations tys@(Forall _ foralls constraints ty) = do

    defCtxt <- fmap defContext get
    -- Clean up knowledge shared between equations of a definition
    modify (\st -> st { guardPredicates = [[]]
                      , patternConsumption = initialisePatternConsumptions equations } )

    elaboratedEquations :: [Equation v Type] <- forM equations $ \equation -> do
        -- Erase the solver predicate between equations
        modify' $ \st -> st
            { predicateStack = []
            , tyVarContext = []
            , guardContexts = []
            , iconsContext = []
            }
        (elaboratedEq, subst) <- checkEquation defCtxt defName equation tys

        -- Solve the generated constraints
        checkerState <- get
        debugM "tyVarContext" . pretty =<< getTyVarContext
        let predStack = Conj $ predicateStack checkerState
        debugM "Solver predicate" $ pretty predStack
        solveConstraints predStack (getSpan equation) defName
        constrStack <- getIConstraints
        solveIConstraints subst constrStack (getSpan equation) tys
        pure elaboratedEq

    checkGuardsForImpossibility s defName
    checkGuardsForExhaustivity s defName ty equations
    pure $ Def s defName elaboratedEquations tys

checkDef :: (?globals :: Globals, Pretty v)
         => Def v ()        -- definition
         -> MaybeT Checker (Def v Type)
checkDef (Def s defName equations tys@(Forall _ foralls _ ty)) =
  checkDef' s defName equations tys

checkEquation :: (?globals :: Globals, Pretty v) =>
     Ctxt TypeScheme -- context of top-level definitions
  -> Id              -- Name of the definition
  -> Equation v ()  -- Equation
  -> TypeScheme      -- Type scheme
  -> MaybeT Checker (Equation v Type, Substitution)

checkEquation defCtxt _ (Equation s () pats expr) tys@(Forall _ foralls constraints ty) = do
  -- Check that the lhs doesn't introduce any duplicate binders
  duplicateBinderCheck s pats

  -- Freshen the type context
  modify (\st -> st { tyVarContext = map (\(n, c) -> (n, (c, ForallQ))) foralls})

  -- Create conjunct to capture the pattern constraints
  newConjunct

  let (predConstrs, iConstrs) = partitionConstraints constraints
  mapM_ (compileAndAddPredicate s) predConstrs
  mapM_ addIConstraint iConstrs

  -- Build the binding context for the branch pattern
  st <- get
  (patternGam, tau, localVars, subst, elaborated_pats, consumptions) <-
     ctxtFromTypedPatterns s ty pats (patternConsumption st)

  -- Update the consumption information
  modify (\st -> st { patternConsumption =
                         zipWith joinConsumption consumptions (patternConsumption st) } )

  -- Create conjunct to capture the body expression constraints
  newConjunct

  -- Specialise the return type by the pattern generated substitution
  debugM "eqn" $ "### -- patternGam = " <> show patternGam
  debugM "eqn" $ "### -- localVars  = " <> show localVars
  debugM "eqn" $ "### -- tau = " <> show tau
  tau' <- substitute subst tau
  debugM "eqn" $ "### -- tau' = " <> show tau'

  -- Check the body
  (localGam, subst', elaboratedExpr) <-
       checkExpr defCtxt patternGam Positive True tau' expr

  case checkLinearity patternGam localGam of
    [] -> do
      localGam <- substitute subst localGam

      -- Check that our consumption context approximations the binding
      ctxtApprox s localGam patternGam

      -- Conclude the implication
      concludeImplication s localVars

      -- Create elaborated equation
      subst'' <- combineSubstitutions s subst subst'
      let elab = Equation s ty elaborated_pats elaboratedExpr

      substituteIConstraints subst''

      elab' <- substitute subst'' elab
      return (elab', subst'')

    -- Anything that was bound in the pattern but not used up
    xs -> illLinearityMismatch s xs

data Polarity = Positive | Negative deriving Show

flipPol :: Polarity -> Polarity
flipPol Positive = Negative
flipPol Negative = Positive

-- Type check an expression

--  `checkExpr defs gam t expr` computes `Just delta`
--  if the expression type checks to `t` in context `gam`:
--  where `delta` gives the post-computation context for expr
--  (which explains the exact coeffect demands)
--  or `Nothing` if the typing does not match.

checkExpr :: (?globals :: Globals, Pretty v)
          => Ctxt TypeScheme   -- context of top-level definitions
          -> Ctxt Assumption   -- local typing context
          -> Polarity         -- polarity of <= constraints
          -> Bool             -- whether we are top-level or not
          -> Type             -- type
          -> Expr v ()       -- expression
          -> MaybeT Checker (Ctxt Assumption, Substitution, Expr v Type)

-- Checking of constants
checkExpr _ [] _ _ ty@(TyCon c) (Val s _ (NumInt n))   | internalName c == "Int" = do
    let elaborated = Val s ty (NumInt n)
    return ([], [], elaborated)

checkExpr _ [] _ _ ty@(TyCon c) (Val s _ (NumFloat n)) | internalName c == "Float" = do
    let elaborated = Val s ty (NumFloat n)
    return ([], [], elaborated)

checkExpr defs gam pol _ ty@(FunTy sig tau) (Val s _ (Abs _ p t e)) = do
  -- If an explicit signature on the lambda was given, then check
  -- it confirms with the type being checked here

  newConjunct

  (tau', subst1) <- case t of
    Nothing -> return (tau, [])
    Just t' -> do
      subst <- fmap equalityProofSubstitution (requireEqualTypes s sig t')
      return (tau, subst)

  (bindings, localVars, subst, elaboratedP, _) <- ctxtFromTypedPattern s sig p NotFull
  debugM "binding from lam" $ pretty bindings

  pIrrefutable <- isIrrefutable s sig p
  if pIrrefutable then do
    -- Check the body in the extended context
    tau'' <- substitute subst tau'

    newConjunct

    (gam', subst2, elaboratedE) <- checkExpr defs (bindings <> gam) pol False tau'' e
    -- Check linearity of locally bound variables
    case checkLinearity bindings gam' of
       [] -> do
          subst <- combineSubstitutions s subst1 subst2

          -- Locally we should have this property (as we are under a binder)
          ctxtEquals s (gam' `intersectCtxts` bindings) bindings

          concludeImplication s localVars

          let elaborated = Val s ty (Abs ty elaboratedP t elaboratedE)

          return (gam' `subtractCtxt` bindings, subst, elaborated)

       xs -> illLinearityMismatch s xs
  else refutablePattern s p

-- Application special case for built-in 'scale'
-- TODO: needs more thought
{- checkExpr defs gam pol topLevel tau
          (App s _ (App _ _ (Val _ _ (Var _ v)) (Val _ _ (NumFloat _ x))) e) | internalName v == "scale" = do
    equalTypesAndUnify s (TyCon $ mkId "Float") tau
    checkExpr defs gam pol topLevel (Box (CFloat (toRational x)) (TyCon $ mkId "Float")) e
-}

-- Application checking
checkExpr defs gam pol topLevel tau (App s _ e1 e2) = do
    (argTy, gam2, subst2, elaboratedR) <- synthExpr defs gam pol e2

    funTy <- substitute subst2 (FunTy argTy tau)
    (gam1, subst1, elaboratedL) <- checkExpr defs gam (flipPol pol) topLevel funTy e1

    gam <- ctxtPlus s gam1 gam2

    subst <- combineSubstitutions s subst1 subst2

    let elaborated = App s tau elaboratedL elaboratedR
    return (gam, subst, elaborated)

{-

[G] |- e : t
 ---------------------
[G]*r |- [e] : []_r t

-}

-- Promotion
checkExpr defs gam pol _ ty@(Box demand tau) (Val s _ (Promote _ e)) = do
    let vars = freeVars e -- map fst gam
    gamF    <- discToFreshVarsIn s vars gam demand
    (gam', subst, elaboratedE) <- checkExpr defs gamF pol False tau e

    -- Causes a promotion of any typing assumptions that came from variable
    -- inside a guard from an enclosing case that have kind Level
    -- This prevents control-flow attacks and is a special case for Level
    -- (the guard contexts come from a special context in the solver)
    guardGam <- allGuardContexts
    guardGam' <- filterM isLevelKinded guardGam
    let gam'' = multAll (vars <> map fst guardGam') demand (gam' <> guardGam')

    let elaborated = Val s ty (Promote tau elaboratedE)
    return (gam'', subst, elaborated)
  where
    -- Calculate whether a type assumption is level kinded
    isLevelKinded (_, as) = do
        ty <- inferCoeffectTypeAssumption s as
        return $ case ty of
          Just (TyCon (internalName -> "Level"))
            -> True
          Just (TyApp (TyCon (internalName -> "Interval"))
                      (TyCon (internalName -> "Level")))
            -> True
          _ -> False


-- Dependent pattern-matching case (only at the top level)
checkExpr defs gam pol True tau (Case s _ guardExpr cases) = do
  -- Synthesise the type of the guardExpr
  (guardTy, guardGam, substG, elaboratedGuard) <- synthExpr defs gam pol guardExpr
  pushGuardContext guardGam

  newCaseFrame

  -- Check each of the branches
  branchCtxtsAndSubst <-
    forM cases $ \(pat_i, e_i) -> do
      -- Build the binding context for the branch pattern
      newConjunct
      (patternGam, eVars, subst, elaborated_pat_i, _) <- ctxtFromTypedPattern s guardTy pat_i NotFull


      -- Checking the case body
      newConjunct
      -- Specialise the return type and the incoming environment using the
      -- pattern-match-generated type substitution
      tau' <- substitute subst tau
      (specialisedGam, unspecialisedGam) <- substCtxt subst gam

      let checkGam = patternGam <> specialisedGam <> unspecialisedGam
      (localGam, subst', elaborated_i) <- checkExpr defs checkGam pol False tau' e_i

      -- We could do this, but it seems redundant.
      -- localGam' <- ctxtPlus s guardGam localGam
      -- ctxtApprox s localGam' checkGam

      -- Check linear use in anything Linear
      gamSoFar <- ctxtPlus s guardGam localGam
      case checkLinearity patternGam gamSoFar of
        -- Return the resulting computed context, without any of
        -- the variable bound in the pattern of this branch
        [] -> do


           debugM "Specialised gam" (pretty specialisedGam)
           debugM "Unspecialised gam" (pretty unspecialisedGam)

           debugM "pattern gam" (pretty patternGam)
           debugM "local gam" (pretty localGam)

           st <- get
           debugM "pred so far" (pretty (predicateStack st))

           -- The resulting context has the shared part removed
           -- 28/02/2018 - We used to have this
           --let branchCtxt = (localGam `subtractCtxt` guardGam) `subtractCtxt` specialisedGam
           -- But we want promotion to invovlve the guard to avoid leaks
           let branchCtxt = (localGam `subtractCtxt` specialisedGam) `subtractCtxt` patternGam

           branchCtxt' <- ctxtPlus s branchCtxt  (justLinear $ (gam `intersectCtxts` specialisedGam) `intersectCtxts` localGam)

           -- Check local binding use
           ctxtApprox s (localGam `intersectCtxts` patternGam) patternGam


           -- Check "global" (to the definition) binding use
           consumedGam <- ctxtPlus s guardGam localGam
           debugM "** gam = " (pretty gam)
           debugM "** c sub p = " (pretty (consumedGam `subtractCtxt` patternGam))

           ctxtApprox s (consumedGam `subtractCtxt` patternGam) gam

           -- Conclude the implication
           concludeImplication (getSpan pat_i) eVars

           return (branchCtxt', subst', (elaborated_pat_i, elaborated_i))

        -- Anything that was bound in the pattern but not used correctly
        xs -> illLinearityMismatch s xs

  st <- get
  debugM "pred so after branches" (pretty (predicateStack st))

  -- All branches must be possible
  checkGuardsForImpossibility s $ mkId "case"

  -- Pop from stacks related to case
  popGuardContext
  popCaseFrame

  -- Find the upper-bound contexts
  let (branchCtxts, substs, elaboratedCases) = unzip3 branchCtxtsAndSubst
  branchesGam <- fold1M (joinCtxts s) branchCtxts

  debugM "*** Branches from the case " (pretty branchCtxts)

  -- Contract the outgoing context of the guard and the branches (joined)
  g <- ctxtPlus s branchesGam guardGam
  debugM "--- Output context for case " (pretty g)

  st <- get
  debugM "pred at end of case" (pretty (predicateStack st))

  let elaborated = Case s tau elaboratedGuard elaboratedCases

  subst <- combineManySubstitutions s substs -- previously concat substs
  return (g, subst, elaborated)

-- All other expressions must be checked using synthesis
checkExpr defs gam pol topLevel tau e = do

  (tau', gam', subst', elaboratedE) <- synthExpr defs gam pol e

  eq <-
    case pol of
      Positive -> do
        debugM "+ Compare for equality " $ pretty tau' <> " = " <> pretty tau
        if topLevel
          -- If we are checking a top-level, then don't allow overapproximation
          then checkEquality (equalTypesWithPolarity (getSpan e) SndIsSpec tau') tau
          else checkEquality (lEqualTypesWithPolarity (getSpan e) SndIsSpec tau') tau

      -- i.e., this check is from a synth
      Negative -> do
        debugM "- Compare for equality " $ pretty tau <> " = " <> pretty tau'
        if topLevel
          -- If we are checking a top-level, then don't allow overapproximation
          then checkEquality (equalTypesWithPolarity (getSpan e) FstIsSpec tau') tau
          else checkEquality (lEqualTypesWithPolarity (getSpan e) FstIsSpec tau') tau

  case eq of
    Right eqres -> do
      let subst = equalityProofSubstitution eqres
      substFinal <- combineSubstitutions (getSpan e) subst subst'
      return (gam', substFinal, elaboratedE)
    _ -> do
      case pol of
        Positive -> typeClash (getSpan e) tau tau'
        Negative -> typeClash (getSpan e) tau' tau

-- | Synthesise the 'Type' of expressions.
-- See <https://en.wikipedia.org/w/index.php?title=Bidirectional_type_checking&redirect=no>
synthExpr :: (?globals :: Globals, Pretty v)
          => Ctxt TypeScheme   -- ^ Context of top-level definitions
          -> Ctxt Assumption   -- ^ Local typing context
          -> Polarity          -- ^ Polarity of subgrading
          -> Expr v ()         -- ^ Expression
          -> MaybeT Checker (Type, Ctxt Assumption, Substitution, Expr v Type)

-- Literals can have their type easily synthesised
synthExpr _ _ _ (Val s _ (NumInt n))  = do
  let t = TyCon $ mkId "Int"
  return (t, [], [], Val s t (NumInt n))

synthExpr _ _ _ (Val s _ (NumFloat n)) = do
  let t = TyCon $ mkId "Float"
  return (t, [], [], Val s t (NumFloat n))

synthExpr _ _ _ (Val s _ (CharLiteral c)) = do
  let t = TyCon $ mkId "Char"
  return (t, [], [], Val s t (CharLiteral c))

synthExpr _ _ _ (Val s _ (StringLiteral c)) = do
  let t = TyCon $ mkId "String"
  return (t, [], [], Val s t (StringLiteral c))

-- Secret syntactic weakening
synthExpr defs gam pol
  (App s _ (Val _ _ (Var _ (sourceName -> "weak__"))) v@(Val _ _ (Var _ x))) = do

  (t, _, subst, elabE) <- synthExpr defs gam pol v

  return (t, [(x, Discharged t (CZero (TyCon $ mkId "Level")))], subst, elabE)

-- Constructors
synthExpr _ gam _ (Val s _ (Constr _ c [])) = do
  -- Should be provided in the type checkers environment
  st <- get
  case lookup c (dataConstructors st) of
    Just (tySch, coercions) -> do
      -- Freshen the constructor
      -- (discarding any fresh type variables, info not needed here)

      -- TODO: allow data type constructors to have constraints
      (ty, _, _, _, coercions') <- freshPolymorphicInstance InstanceQ False tySch coercions

      -- Apply coercions
      ty <- substitute coercions' ty

      let elaborated = Val s ty (Constr ty c [])
      return (ty, [], [], elaborated)

    Nothing -> halt $ UnboundVariableError (Just s) $
              "Data constructor `" <> pretty c <> "`" <?> show (dataConstructors st)

-- Case synthesis
synthExpr defs gam pol (Case s _ guardExpr cases) = do
  -- Synthesise the type of the guardExpr
  (ty, guardGam, substG, elaboratedGuard) <- synthExpr defs gam pol guardExpr
  -- then synthesise the types of the branches

  newCaseFrame

  branchTysAndCtxtsAndSubsts <-
    forM cases $ \(pati, ei) -> do
      -- Build the binding context for the branch pattern
      newConjunct
      (patternGam, eVars, _, elaborated_pat_i, _) <- ctxtFromTypedPattern s ty pati NotFull
      newConjunct
      ---
      (tyCase, localGam, subst', elaborated_i) <- synthExpr defs (patternGam <> gam) pol ei
      concludeImplication (getSpan pati) eVars

      ctxtEquals s (localGam `intersectCtxts` patternGam) patternGam

      -- Check linear use in this branch
      gamSoFar <- ctxtPlus s guardGam localGam
      case checkLinearity patternGam gamSoFar of
         -- Return the resulting computed context, without any of
         -- the variable bound in the pattern of this branch
         [] -> return (tyCase, (localGam `subtractCtxt` patternGam, subst'),
                        (elaborated_pat_i, elaborated_i))
         xs -> illLinearityMismatch s xs

  -- All branches must be possible
  checkGuardsForImpossibility s $ mkId "case"

  popCaseFrame

  let (branchTys, branchCtxtsAndSubsts, elaboratedCases) = unzip3 branchTysAndCtxtsAndSubsts
  let (branchCtxts, branchSubsts) = unzip branchCtxtsAndSubsts
  let branchTysAndSpans = zip branchTys (map (getSpan . snd) cases)
  -- Finds the upper-bound return type between all branches
  branchType <- foldM (\ty2 (ty1, sp) -> joinTypes sp ty1 ty2)
                   (head branchTys)
                   (tail branchTysAndSpans)

  -- Find the upper-bound type on the return contexts
  branchesGam <- fold1M (joinCtxts s) branchCtxts

  -- Contract the outgoing context of the guard and the branches (joined)
  gamNew <- ctxtPlus s branchesGam guardGam

  debugM "*** synth branchesGam" (pretty branchesGam)

  subst <- combineManySubstitutions s branchSubsts
  subst <- combineSubstitutions s substG subst

  let elaborated = Case s branchType elaboratedGuard elaboratedCases
  return (branchType, gamNew, subst, elaborated)

-- Diamond cut
synthExpr defs gam pol (LetDiamond s _ p optionalTySig e1 e2) = do
  -- TODO: refactor this once we get a proper mechanism for
  -- specifying effect over-approximations and type aliases

  (sig, gam1, subst1, elaborated1) <- synthExpr defs gam pol e1

  (ef1, ty1) <-
          case sig of
            Diamond ["IO"] ty1 -> return ([], ty1)
            Diamond ["Session"] ty1 -> return ([], ty1)
            Diamond ef1 ty1 -> return (ef1, ty1)
            t -> halt $ GenericError (Just s)
                   $ "Expected a graded effect type of the form `t <e>` type but got `"
                  <> pretty t <> "` in subject of let"

  -- Type body of the let...
  -- ...in the context of the binders from the pattern
  (binders, _, substP, elaboratedP, _)  <- ctxtFromTypedPattern s ty1 p NotFull
  pIrrefutable <- isIrrefutable s ty1 p
  if not pIrrefutable
  then refutablePattern s p
  else do
     (tau, gam2, subst2, elaborated2) <- synthExpr defs (binders <> gam) pol e2
     (ef2, ty2) <-
           case tau of
             Diamond ["IO"] ty2 -> return ([], ty2)
             Diamond ["Session"] ty2 -> return ([], ty2)
             Diamond ef2 ty2 -> return (ef2, ty2)
             t -> halt $ GenericError (Just s)
                    $ "Expecting a graded effect type of the form `t <e>` but got `"
                    <> pretty t <> "` in body of let"

     optionalSigEquality s optionalTySig ty1

     -- Check that usage matches the binding grades/linearity
     -- (performs the linearity check)
     ctxtEquals s (gam2 `intersectCtxts` binders) binders

     gamNew <- ctxtPlus s (gam2 `subtractCtxt` binders) gam1

     let t = Diamond (ef1 <> ef2) ty2

     subst <- combineManySubstitutions s [substP, subst1, subst2]
     -- Synth subst
     t' <- substitute substP t

     let elaborated = LetDiamond s t elaboratedP optionalTySig elaborated1 elaborated2
     return (t, gamNew, subst, elaborated)

-- Variables
synthExpr defs gam _ (Val s _ (Var _ x)) =
   -- Try the local context
   case lookup x gam of
     Nothing ->
       -- Try definitions in scope
       case lookup x (defs <> Primitives.builtins) of
         Just tyScheme  -> do
           (ty', _, _, (constraints, iconstraints), []) <- freshPolymorphicInstance InstanceQ False tyScheme [] -- discard list of fresh type variables

           mapM_ (compileAndAddPredicate s) constraints
           mapM_ addIConstraint iconstraints

           let elaborated = Val s ty' (Var ty' x)
           return (ty', [], [], elaborated)

         -- Couldn't find it
         Nothing  -> halt $ UnboundVariableError (Just s) $ pretty x <?> "synthExpr on variables"
                              <> if debugging ?globals then
                                  " { looking for " <> show x
                                  <> " in context " <> show gam
                                  <> "}"
                                 else ""
     -- In the local context
     Just (Linear ty)       -> do
       let elaborated = Val s ty (Var ty x)
       return (ty, [(x, Linear ty)], [], elaborated)

     Just (Discharged ty c) -> do
       k <- inferCoeffectType s c
       let elaborated = Val s ty (Var ty x)
       return (ty, [(x, Discharged ty (COne k))], [], elaborated)

-- Specialised application for scale
{-
TODO: needs thought
synthExpr defs gam pol
      (App _ _ (Val _ _ (Var _ v)) (Val _ _ (NumFloat _ r))) | internalName v == "scale" = do
  let float = TyCon $ mkId "Float"
  return (FunTy (Box (CFloat (toRational r)) float) float, [])
-}

-- Application
synthExpr defs gam pol (App s _ e e') = do
    (fTy, gam1, subst1, elaboratedL) <- synthExpr defs gam pol e
    case fTy of
      -- Got a function type for the left-hand side of application
      (FunTy sig tau) -> do
         (gam2, subst2, elaboratedR) <- checkExpr defs gam (flipPol pol) False sig e'
         gamNew <- ctxtPlus s gam1 gam2

         subst <- combineSubstitutions s subst1 subst2

         -- Synth subst
         tau    <- substitute subst tau

         substituteIConstraints subst

         elaborated <- substitute subst (App s tau elaboratedL elaboratedR)
         return (tau, gamNew, subst, elaborated)

      -- Not a function type
      t ->
        halt $ GenericError (Just s) $ "Left-hand side of application is not a function"
                   <> " but has type '" <> pretty t <> "'"

{- Promotion

[G] |- e : t
 ---------------------
[G]*r |- [e] : []_r t

-}

synthExpr defs gam pol (Val s _ (Promote _ e)) = do
   debugM "Synthing a promotion of " $ pretty e

   -- Create a fresh kind variable for this coeffect
   vark <- freshIdentifierBase $ "kprom_" <> [head (pretty e)]
   -- remember this new kind variable in the kind environment
   modify (\st -> st { tyVarContext = (mkId vark, (KCoeffect, InstanceQ)) : tyVarContext st })

   -- Create a fresh coeffect variable for the coeffect of the promoted expression
   var <- freshTyVarInContext (mkId $ "prom_[" <> pretty e <> "]") (KPromote $ TyVar $ mkId vark)

   gamF <- discToFreshVarsIn s (freeVars e) gam (CVar var)

   (t, gam', subst, elaboratedE) <- synthExpr defs gamF pol e

   let finalTy = Box (CVar var) t
   let elaborated = Val s finalTy (Promote t elaboratedE)
   return (finalTy, multAll (freeVars e) (CVar var) gam', subst, elaborated)


-- BinOp
synthExpr defs gam pol (Binop s _ op e1 e2) = do
    (t1, gam1, subst1, elaboratedL) <- synthExpr defs gam pol e1
    (t2, gam2, subst2, elaboratedR) <- synthExpr defs gam pol e2
    -- Look through the list of operators (of which there might be
    -- multiple matching operators)
    case lookupMany op Primitives.binaryOperators of
      [] -> halt $ UnboundVariableError (Just s) $ "Binary operator " <> op
      ops -> do
        returnType <- selectFirstByType t1 t2 ops
        gamOut <- ctxtPlus s gam1 gam2

        subst <- combineSubstitutions s subst1 subst2

        let elaborated = Binop s returnType op elaboratedL elaboratedR
        return (returnType, gamOut, subst, elaborated)

  where
    -- No matching type were found (meaning there is a type error)
    selectFirstByType t1 t2 [] =
      halt $ GenericError (Just s) $ "Could not resolve operator " <> op <> " at type: "
         <> pretty (FunTy t1 (FunTy t2 (TyVar $ mkId "...")))

    selectFirstByType t1 t2 ((FunTy opt1 (FunTy opt2 resultTy)):ops) = do
      -- Attempt to use this typing
      (result, local) <- localChecking $ do
         eq1 <- typesAreEqualWithCheck s t1 opt1
         eq2 <- typesAreEqualWithCheck s t2 opt2
         return (eq1 && eq2)
      -- If successful then return this local computation
      case result of
        Just True -> local >> return resultTy
        _         -> selectFirstByType t1 t2 ops

    selectFirstByType t1 t2 (_:ops) = selectFirstByType t1 t2 ops


-- Abstraction, can only synthesise the types of
-- lambda in Church style (explicit type)
synthExpr defs gam pol (Val s _ (Abs _ p (Just sig) e)) = do

  newConjunct

  (bindings, localVars, substP, elaboratedP, _) <- ctxtFromTypedPattern s sig p NotFull

  newConjunct

  pIrrefutable <- isIrrefutable s sig p
  if pIrrefutable then do
     (tau, gam'', subst, elaboratedE) <- synthExpr defs (bindings <> gam) pol e

     -- Locally we should have this property (as we are under a binder)
     ctxtEquals s (gam'' `intersectCtxts` bindings) bindings

     let finalTy = FunTy sig tau
     let elaborated = Val s finalTy (Abs finalTy elaboratedP (Just sig) elaboratedE)

     substFinal <- combineSubstitutions s substP subst
     finalTy' <- substitute substP finalTy

     concludeImplication s localVars

     return (finalTy', gam'' `subtractCtxt` bindings, substFinal, elaborated)

  else refutablePattern s p

-- Abstraction, can only synthesise the types of
-- lambda in Church style (explicit type)
synthExpr defs gam pol (Val s _ (Abs _ p Nothing e)) = do

  newConjunct

  tyVar <- freshTyVarInContext (mkId "t") KType
  let sig = (TyVar tyVar)

  (bindings, localVars, substP, elaboratedP, _) <- ctxtFromTypedPattern s sig p NotFull

  newConjunct

  pIrrefutable <- isIrrefutable s sig p
  if pIrrefutable then do
     (tau, gam'', subst, elaboratedE) <- synthExpr defs (bindings <> gam) pol e

     -- Locally we should have this property (as we are under a binder)
     ctxtEquals s (gam'' `intersectCtxts` bindings) bindings

     let finalTy = FunTy sig tau
     let elaborated = Val s finalTy (Abs finalTy elaboratedP (Just sig) elaboratedE)
     finalTy' <- substitute substP finalTy

     concludeImplication s localVars

     subst <- combineSubstitutions s substP subst

     return (finalTy', gam'' `subtractCtxt` bindings, subst, elaborated)
  else refutablePattern s p

synthExpr _ _ _ e =
  halt $ GenericError (Just $ getSpan e) $ "Type cannot be calculated here for `"
      <> pretty e <> "` try adding more type signatures."

-- Check an optional type signature for equality against a type
optionalSigEquality :: (?globals :: Globals) => Span -> Maybe Type -> Type -> MaybeT Checker Bool
optionalSigEquality _ Nothing _ = return True
optionalSigEquality s (Just t) t' = typesAreEqualWithCheck s t' t


solveConstraintsSafe :: (?globals :: Globals) => Pred -> Span -> Id -> MaybeT Checker (Maybe [CheckerError])
solveConstraintsSafe predicate s name = do
  -- Get the coeffect kind context and constraints
  checkerState <- get
  let ctxtCk  = tyVarContext checkerState
  coeffectVars <- justCoeffectTypesConverted s ctxtCk

  result <- liftIO $ provePredicate s predicate coeffectVars

  case result of
    QED -> success
    NotValid msg -> do
       msg' <- rewriteMessage msg
       simpPred <- simplifyPred predicate

       failed . pure . GenericError (Just s) $ "The associated theorem for `" <> pretty name <> "` "
          <> if msg' == "is Falsifiable\n"
              then  "is false. "
                 <> "\n  That is: " <> pretty (NegPred simpPred)
              else msg' <> "\n  thus: "  <> pretty (NegPred simpPred)

    NotValidTrivial unsats ->
       failed $ fmap (\c -> GradingError (Just $ getSpan c) (pretty . Neg $ c)) unsats
    Timeout ->
       halt $ CheckerError (Just s) $
         "Solver timed out with limit of " <>
         show (solverTimeoutMillis ?globals) <>
         " ms. You may want to increase the timeout (see --help)."
    Error msg ->
       halt msg
    where failed = pure . Just
          success = pure Nothing


solveConstraints :: (?globals :: Globals) => Pred -> Span -> Id -> MaybeT Checker ()
solveConstraints predicate s name = do
  res <- solveConstraintsSafe predicate s name
  maybe (pure ()) (mapM_ halt) res


solveIConstraints :: (?globals :: Globals) => Substitution -> [Inst] -> Span -> TypeScheme -> MaybeT Checker ()
solveIConstraints coercions itys sp tys = do
  itys' <- mapM (substitute coercions) itys
  topLevelExpanded <- mapM (substitute coercions) =<< getExpandedContext sp tys
  let remaining = itys' \\ topLevelExpanded
  mapM_ solveIConstraint remaining
    where solveIConstraint = verifyInstanceExists sp


-- Rewrite an error message coming from the solver
rewriteMessage :: String -> MaybeT Checker String
rewriteMessage msg = do
    st <- get
    let tyVars = tyVarContext st
    let msgLines = T.lines $ T.pack msg
    -- Rewrite internal names to source names
    let msgLines' = map (\line -> foldl convertLine line tyVars) msgLines

    return $ T.unpack (T.unlines msgLines')
  where
    convertLine line (v, (k, _)) =
        -- Try to replace line variables in the line
       let line' = T.replace (T.pack (internalName v)) (T.pack (sourceName v)) line
       -- If this succeeds we might want to do some other replacements
           line'' =
             if line /= line' then
               case k of
                 KPromote (TyCon (internalName -> "Level")) ->
                    T.replace (T.pack $ show privateRepresentation) (T.pack "Private")
                      (T.replace (T.pack $ show publicRepresentation) (T.pack "Public")
                       (T.replace (T.pack "Integer") (T.pack "Level") line'))
                 _ -> line'
             else line'
       in line''

justCoeffectTypesConverted s xs = mapM convert xs >>= (return . catMaybes)
  where
    convert (var, (KPromote t, q)) = do
      k <- inferKindOfType s t
      case k of
        KCoeffect -> return $ Just (var, (t, q))
        _         -> return Nothing
    convert (var, (KVar v, q)) = do
      k <- inferKindOfType s (TyVar v)
      case k of
        KCoeffect -> return $ Just (var, (TyVar v, q))
        _         -> return Nothing
    convert _ = return Nothing

justCoeffectTypesConvertedVars s env = do
  let implicitUniversalMadeExplicit = map (\(var, k) -> (var, (k, ForallQ))) env
  env' <- justCoeffectTypesConverted s implicitUniversalMadeExplicit
  return $ stripQuantifiers env'

-- | `ctxtEquals ctxt1 ctxt2` checks if two contexts are equal
--   and the typical pattern is that `ctxt2` represents a specification
--   (i.e. input to checking) and `ctxt1` represents actually usage
ctxtApprox :: (?globals :: Globals) =>
    Span -> Ctxt Assumption -> Ctxt Assumption -> MaybeT Checker ()
ctxtApprox s ctxt1 ctxt2 = do
  -- intersection contains those ids from ctxt1 which appears in ctxt2
  intersection <-
    -- For everything in the right context
    -- (which should come as an input to checking)
    forM ctxt2 $ \(id, ass2) ->
      -- See if it appears in the left context...
      case lookup id ctxt1 of
        -- ... if so equate
        Just ass1 -> do
          relateByAssumption s ApproximatedBy (id, ass1) (id, ass2)
          return id
        -- ... if not check to see if the missing variable is linear
        Nothing   ->
           case ass2 of
             -- Linear gets instantly reported
             Linear t -> illLinearityMismatch s [LinearNotUsed id]
             -- Else, this could be due to weakening so see if this is allowed
             Discharged t c -> do
               kind <- inferCoeffectType s c
               relateByAssumption s ApproximatedBy (id, Discharged t (CZero kind)) (id, ass2)
               return id
  -- Last we sanity check, if there is anything in ctxt1 that is not in ctxt2
  -- then we have an issue!
  forM_ ctxt1 $ \(id, ass1) ->
    if (id `elem` intersection)
      then return ()
      else halt $ UnboundVariableError (Just s) $
                "Variable `" <> pretty id <> "` was used but is not bound here"


-- | `ctxtEquals ctxt1 ctxt2` checks if two contexts are equal
--   and the typical pattern is that `ctxt2` represents a specification
--   (i.e. input to checking) and `ctxt1` represents actually usage
ctxtEquals :: (?globals :: Globals) =>
    Span -> Ctxt Assumption -> Ctxt Assumption -> MaybeT Checker ()
ctxtEquals s ctxt1 ctxt2 = do
  -- intersection contains those ids from ctxt1 which appears in ctxt2
  intersection <-
    -- For everything in the right context
    -- (which should come as an input to checking)
    forM ctxt2 $ \(id, ass2) ->
      -- See if it appears in the left context...
      case lookup id ctxt1 of
        -- ... if so equate
        Just ass1 -> do
          relateByAssumption s Eq (id, ass1) (id, ass2)
          return id
        -- ... if not check to see if the missing variable is linear
        Nothing   ->
           case ass2 of
             -- Linear gets instantly reported
             Linear t -> illLinearityMismatch s [LinearNotUsed id]
             -- Else, this could be due to weakening so see if this is allowed
             Discharged t c -> do
               kind <- inferCoeffectType s c
               relateByAssumption s Eq (id, Discharged t (CZero kind)) (id, ass2)
               return id
  -- Last we sanity check, if there is anything in ctxt1 that is not in ctxt2
  -- then we have an issue!
  forM_ ctxt1 $ \(id, ass1) ->
    if (id `elem` intersection)
      then return ()
      else halt $ UnboundVariableError (Just s) $
                "Variable `" <> pretty id <> "` was used but is not bound here"

{- | Take the least-upper bound of two contexts.
     If one context contains a linear variable that is not present in
    the other, then the resulting context will not have this linear variable -}
joinCtxts :: (?globals :: Globals) => Span -> Ctxt Assumption -> Ctxt Assumption
  -> MaybeT Checker (Ctxt Assumption)
joinCtxts s ctxt1 ctxt2 = do
    -- All the type assumptions from ctxt1 whose variables appear in ctxt2
    -- and weaken all others
    ctxt  <- intersectCtxtsWithWeaken s ctxt1 ctxt2
    -- All the type assumptions from ctxt2 whose variables appear in ctxt1
    -- and weaken all others
    ctxt' <- intersectCtxtsWithWeaken s ctxt2 ctxt1

    -- Make an context with fresh coeffect variables for all
    -- the variables which are in both ctxt1 and ctxt2...
    varCtxt <- freshVarsIn s (map fst ctxt) ctxt

    -- ... and make these fresh coeffects the upper-bound of the coeffects
    -- in ctxt and ctxt'
    zipWithM_ (relateByAssumption s ApproximatedBy) ctxt varCtxt
    zipWithM_ (relateByAssumption s ApproximatedBy) ctxt' varCtxt
    -- Return the common upper-bound context of ctxt1 and ctxt2
    return varCtxt

{- |  intersect contexts and weaken anything not appear in both
        relative to the left context (this is not commutative) -}
intersectCtxtsWithWeaken :: (?globals :: Globals) => Span -> Ctxt Assumption -> Ctxt Assumption
  -> MaybeT Checker (Ctxt Assumption)
intersectCtxtsWithWeaken s a b = do
   let intersected = intersectCtxts a b
   -- All the things that were not shared
   let remaining   = b `subtractCtxt` intersected
   let leftRemaining = a `subtractCtxt` intersected
   weakenedRemaining <- mapM weaken remaining
   let newCtxt = intersected <> filter isNonLinearAssumption (weakenedRemaining <> leftRemaining)
   return . normaliseCtxt $ newCtxt
  where
   isNonLinearAssumption :: (Id, Assumption) -> Bool
   isNonLinearAssumption (_, Discharged _ _) = True
   isNonLinearAssumption _                   = False

   weaken :: (Id, Assumption) -> MaybeT Checker (Id, Assumption)
   weaken (var, Linear t) =
       return (var, Linear t)
   weaken (var, Discharged t c) = do
       kind <- inferCoeffectType s c
       return (var, Discharged t (CZero kind))

{- | Given an input context and output context, check the usage of
     variables in the output, returning a list of usage mismatch
     information if, e.g., a variable is bound linearly in the input but is not
     used in the output, or is discharged in the output -}
checkLinearity :: Ctxt Assumption -> Ctxt Assumption -> [LinearityMismatch]
checkLinearity [] _ = []
checkLinearity ((v, Linear _):inCtxt) outCtxt =
  case lookup v outCtxt of
    -- Good: linear variable was used
    Just Linear{} -> checkLinearity inCtxt outCtxt
    -- Bad: linear variable was discharged (boxed var but binder not unboxed)
    Just Discharged{} -> LinearUsedNonLinearly v : checkLinearity inCtxt outCtxt
    Nothing -> LinearNotUsed v : checkLinearity inCtxt outCtxt

checkLinearity ((_, Discharged{}):inCtxt) outCtxt =
  -- Discharged things can be discarded, so it doesn't matter what
  -- happens with them
  checkLinearity inCtxt outCtxt

relateByAssumption :: (?globals :: Globals)
  => Span
  -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
  -> (Id, Assumption)
  -> (Id, Assumption)
  -> MaybeT Checker ()

-- Linear assumptions ignored
relateByAssumption _ _ (_, Linear _) (_, Linear _) = return ()

-- Discharged coeffect assumptions
relateByAssumption s rel (_, Discharged _ c1) (_, Discharged _ c2) = do
  kind <- mguCoeffectTypes s c1 c2
  addConstraint (rel s c1 c2 kind)

relateByAssumption s _ x y =
  halt $ GenericError (Just s) $ "Can't unify free-variable types:\n\t"
           <> "(graded) " <> pretty x <> "\n  with\n\t(linear) " <> pretty y

-- Replace all top-level discharged coeffects with a variable
-- and derelict anything else
-- but add a var
discToFreshVarsIn :: (?globals :: Globals) => Span -> [Id] -> Ctxt Assumption -> Coeffect
  -> MaybeT Checker (Ctxt Assumption)
discToFreshVarsIn s vars ctxt coeffect = mapM toFreshVar (relevantSubCtxt vars ctxt)
  where
    toFreshVar (var, Discharged t c) = do
      coeffTy <- mguCoeffectTypes s c coeffect
      return (var, Discharged t (CSig c coeffTy))

    toFreshVar (var, Linear t) = do
      coeffTy <- inferCoeffectType s coeffect
      return (var, Discharged t (COne coeffTy))


-- `freshVarsIn names ctxt` creates a new context with
-- all the variables names in `ctxt` that appear in the list
-- `vars` and are discharged are
-- turned into discharged coeffect assumptions annotated
-- with a fresh coeffect variable (and all variables not in
-- `vars` get deleted).
-- e.g.
--  `freshVarsIn ["x", "y"] [("x", Discharged (2, Int),
--                           ("y", Linear Int),
--                           ("z", Discharged (3, Int)]
--  -> [("x", Discharged (c5 :: Nat, Int),
--      ("y", Linear Int)]
--
freshVarsIn :: (?globals :: Globals) => Span -> [Id] -> Ctxt Assumption
  -> MaybeT Checker (Ctxt Assumption)
freshVarsIn s vars ctxt = mapM toFreshVar (relevantSubCtxt vars ctxt)
  where
    toFreshVar (var, Discharged t c) = do
      ctype <- inferCoeffectType s c
      -- Create a fresh variable
      freshName <- freshIdentifierBase (internalName var)
      let cvar = mkId freshName
      -- Update the coeffect kind context
      modify (\s -> s { tyVarContext = (cvar, (promoteTypeToKind ctype, InstanceQ)) : tyVarContext s })

      -- Return the freshened var-type mapping
      return (var, Discharged t (CVar cvar))

    toFreshVar (var, Linear t) = return (var, Linear t)


-- Combine two contexts
ctxtPlus :: (?globals :: Globals) => Span -> Ctxt Assumption -> Ctxt Assumption
  -> MaybeT Checker (Ctxt Assumption)
ctxtPlus _ [] ctxt2 = return ctxt2
ctxtPlus s ((i, v) : ctxt1) ctxt2 = do
  ctxt' <- extCtxt s ctxt2 i v
  ctxtPlus s ctxt1 ctxt'

-- ExtCtxt the context
extCtxt :: (?globals :: Globals) => Span -> Ctxt Assumption -> Id -> Assumption
  -> MaybeT Checker (Ctxt Assumption)
extCtxt s ctxt var (Linear t) = do

  case lookup var ctxt of
    Just (Linear t') ->
       if t == t'
        then halt $ LinearityError (Just s)
                  $ "Linear variable `" <> pretty var <> "` is used more than once.\n"
        else typeClashForVariable s var t t'
    Just (Discharged t' c) ->
       if t == t'
         then do
           k <- inferCoeffectType s c
           return $ replace ctxt var (Discharged t (c `CPlus` COne k))
         else typeClashForVariable s var t t'
    Nothing -> return $ (var, Linear t) : ctxt

extCtxt s ctxt var (Discharged t c) = do

  case lookup var ctxt of
    Just (Discharged t' c') ->
        if t == t'
        then return $ replace ctxt var (Discharged t' (c `CPlus` c'))
        else typeClashForVariable s var t t'
    Just (Linear t') ->
        if t == t'
        then do
           k <- inferCoeffectType s c
           return $ replace ctxt var (Discharged t (c `CPlus` COne k))
        else typeClashForVariable s var t t'
    Nothing -> return $ (var, Discharged t c) : ctxt

-- Helper, foldM on a list with at least one element
fold1M :: Monad m => (a -> a -> m a) -> [a] -> m a
fold1M _ []     = error "Must have at least one case"
fold1M f (x:xs) = foldM f x xs

justLinear [] = []
justLinear ((x, Linear t) : xs) = (x, Linear t) : justLinear xs
justLinear ((x, _) : xs) = justLinear xs

checkGuardsForExhaustivity :: (?globals :: Globals)
  => Span -> Id -> Type -> [Equation v ()] -> MaybeT Checker ()
checkGuardsForExhaustivity s name ty eqs = do
  -- TODO:
  return ()

checkGuardsForImpossibility :: (?globals :: Globals) => Span -> Id -> MaybeT Checker ()
checkGuardsForImpossibility s name = do
  -- Get top of guard predicate stack
  st <- get
  let ps : _ = guardPredicates st

  -- Convert all universal variables to existential
  let tyVarContextExistential =
         mapMaybe (\(v, (k, q)) ->
                       case q of
                         BoundQ -> Nothing
                         _      -> Just (v, (k, InstanceQ))) (tyVarContext st)
  tyVars <- justCoeffectTypesConverted s tyVarContextExistential

  -- For each guard predicate
  forM_ ps $ \((ctxt, p), s) -> do

    p <- simplifyPred p

    -- Existentially quantify those variables occuring in the pattern in scope
    let thm = foldr (uncurry Exists) p ctxt

    debugM "impossibility" $ "about to try" <> pretty thm
    -- Try to prove the theorem
    result <- liftIO $ provePredicate s thm tyVars

    let msgHead = "Pattern guard for equation of `" <> pretty name <> "`"

    case result of
      QED -> return ()

      -- Various kinds of error
      NotValid msg -> do
        simpPred <- simplifyPred p
        halt $ GenericError (Just s) $ msgHead
                    <> " is impossible. Its condition "
                    <>  if msg == "is Falsifiable\n"
                            then  "is false. "
                               <> "\n  That is: " <> pretty (NegPred simpPred)
                            else msg <> "\n  thus: "  <> pretty (NegPred simpPred)

      NotValidTrivial unsats ->
                      halt $ GenericError (Just s) $ msgHead <>
                        " is impossible.\n\t" <>
                        intercalate "\n\t" (map (pretty . Neg) unsats)
      Timeout -> halt $ CheckerError (Just s) $
         "While checking plausibility of pattern guard for equation " <> pretty name
         <> "the solver timed out with limit of " <>
         show (solverTimeoutMillis ?globals) <>
         " ms. You may want to increase the timeout (see --help)."

      Error msg -> halt msg


-------------------
----- Helpers -----
-------------------


-- TODO: move this into Checker.Monad or Checker.Interface (these depend
--       on Checker.Substitutions, so there is a recursive import
--       - GuiltyDolphin (2019-02-22)
-- | Perform a substitution on the current interface constraint context.
substituteIConstraints :: (?globals :: Globals) => Substitution -> MaybeT Checker ()
substituteIConstraints subst =
  getIConstraints >>= mapM (substitute subst) >>= putIcons


expandIConstraints :: (?globals :: Globals) => Span -> [Inst] -> MaybeT Checker [Inst]
expandIConstraints sp icons = fmap (nub . concat) $ mapM expandIConstraint icons
  where expandIConstraint c = do
          parents <- getInterfaceDependenciesFlattened c
          pure (c : parents)
        getInterfaceDependenciesFlattened c = do
          parents <- getInterfaceConstraints' sp c
          parentsFlat <- fmap concat $ mapM getInterfaceDependenciesFlattened parents
          pure $ parents <> parentsFlat


-- | Retrieve the expanded interface context from the typescheme.
getExpandedContext :: (?globals :: Globals) => Span -> TypeScheme -> MaybeT Checker [Inst]
getExpandedContext sp = expandIConstraints sp . iconsFromTys


verifyInstanceExists :: (?globals :: Globals) => Span -> Inst -> MaybeT Checker ()
verifyInstanceExists sp inst = do
  maybeInst <- getInstance sp inst
  case maybeInst of
    Nothing -> halt $ GenericError (Just sp) $ "No instance for " <> prettyQuoted inst
    Just _ -> pure ()


getInterfaceConstraints' :: (?globals :: Globals) => Span -> Inst -> MaybeT Checker [Inst]
getInterfaceConstraints' sp inst = do
  let iname = instIFace inst
      ipars = instParams inst
  params <- getInterfaceParameterNames sp iname
  constrs <- getInterfaceConstraints sp iname
  let subst = fmap (\(v,t) -> (v, SubstT t)) (zip params ipars)
  mapM (substitute subst) constrs


-- | Verify that the constraint is valid.
verifyConstraint :: (?globals :: Globals) => Span -> Inst -> MaybeT Checker ()
verifyConstraint sp cty = verifyInstanceExists sp cty


-- | Execute a checker with context from the instance head in scope.
withInstanceContext :: (?globals :: Globals) => Span -> Inst -> MaybeT Checker a -> MaybeT Checker a
withInstanceContext sp inst c = do
  tyVars <- getInstanceFreeVarKinds sp inst
  withBindings tyVars InstanceQ c


-- | Get the interface context of a typescheme.
iconsFromTys :: TypeScheme -> [Inst]
iconsFromTys (Forall _ _ constrs _) = constrsToIcons constrs


constrsToIcons :: [Type] -> [Inst]
constrsToIcons = catMaybes . fmap instFromTy


constrsFromIcons :: [Inst] -> [Type]
constrsFromIcons = fmap tyFromInst


mkIFaceApp :: Id -> [Id] -> Type
mkIFaceApp iname = tyFromInst . mkInst iname . fmap TyVar


-- | Normalise the kind of the parameter, giving it a sensible
-- | default if no explicit kind signature is given.
normaliseParameterKind :: (Id, Maybe Kind) -> (Id, Kind)
normaliseParameterKind = second inferParameterKind
  where inferParameterKind = fromMaybe KType


getInstanceFreeVarKinds :: (?globals :: Globals) => Span -> Inst -> MaybeT Checker [(Id, Kind)]
getInstanceFreeVarKinds sp inst = do
  kinds <- getInterfaceParameterKindsForInst sp inst
  getParamsFreeVarKinds sp (zip kinds (instParams inst))


-- | True if the two instances can be proven to be equal in the current context.
instancesAreEqual' :: (?globals :: Globals) => Span -> Inst -> Inst -> MaybeT Checker Bool
instancesAreEqual' sp t1 t2 = do
 res <- equalInstances sp t1 t2
 case res of
   Left{}   -> pure False
   Right pf -> do
     equalityPreds <- substitute (equalityProofSubstitution pf) (equalityProofConstraints pf)
     preds <- get >>= (substitute (equalityProofSubstitution pf) . predicateStack)
     let eqPred = Conj . fmap Con $ equalityPreds
         toSolve = Conj [Conj preds, eqPred]
     fmap (maybe True (const False)) $ solveConstraintsSafe toSolve sp (mkId "$internal")


unboundKindVariable :: (?globals :: Globals) => Span -> Id -> MaybeT Checker a
unboundKindVariable sp n =
  halt $ UnboundVariableError (Just sp) $
       concat ["Kind variable ", prettyQuoted n, " could not be found in context."]


------------------------------
----- Constraint Helpers -----
------------------------------


-- | Constrain the typescheme with the given constraint.
constrain :: (?globals :: Globals) => [Inst] -> TypeScheme -> MaybeT Checker TypeScheme
constrain constrs (Forall sp binds constrs' ty) = do
  fvks <- fmap concat $ mapM (getInstanceFreeVarKinds sp) constrs
  pure $ Forall sp (binds <> fvks) (fmap tyFromInst constrs <> constrs') ty


infixr 6 |>
(|>) :: (?globals :: Globals) => [Inst] -> MaybeT Checker TypeScheme -> MaybeT Checker TypeScheme
constrs |> tys = tys >>= constrain constrs


-- | Get the instantiated form of an interface at the point of a constraint.
-- |
-- | We require that both the interface and constraint are valid at the point
-- | of call.
instantiateInterface :: (?globals :: Globals) => Span -> Inst
                     -> MaybeT Checker
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
validateConstraint :: (?globals :: Globals) => Span -> Inst -> MaybeT Checker ()
validateConstraint sp inst = do
  let iname = instIFace inst

  -- verify that the associated interface is in scope
  checkIFaceExists sp iname

  -- make sure the number of parameters is correct
  let numParams = length (instParams inst)
  expectedNumParams <- fmap length (getInterfaceParameterNames sp iname)
  when (numParams /= expectedNumParams) $
    halt $ GenericError (Just sp) $
      concat [ "Wrong number of parameters in instance ", prettyQuoted inst, "."
             , " Expected ", show expectedNumParams, " but got ", show numParams, "."]

  -- Make sure the constraint parameters are well-kinded
  -- with respect to the interface parameters (ensuring
  -- kind dependencies are resolved)
  withInstanceContext sp inst $ kindCheckConstraint sp inst

  -- Make sure all of the interface constraints are
  -- satisfiable in the context
  icons <- getInterfaceConstraints' sp inst
  mapM_ (verifyConstraint sp) icons


-- | Kind check the given type, treating it as an interface constraint.
kindCheckConstraintType :: (?globals :: Globals) => Span -> Type -> MaybeT Checker ()
kindCheckConstraintType sp ty = requireKind ty (KConstraint InterfaceC)
  where requireKind t reqKind = do
          kind <- inferKindOfType sp t
          when (kind /= reqKind) $ illKindedNEq sp reqKind kind


-- | Check that all the constraint parameters are well-kinded with respect
-- | to the interface, in the current context.
kindCheckConstraint :: (?globals :: Globals) => Span -> Inst -> MaybeT Checker Substitution
kindCheckConstraint sp inst = do
  -- make sure we are dealing with an interface
  let iname = instIFace inst
  termKind <- getTerminalKind iname
  when (termKind /= KConstraint InterfaceC) $
    halt . KindError (Just sp)
           $ prettyQuoted inst <> " does not represent an interface constraint."

  -- check every parameter is well-kinded with respect to the interface
  kinds <- getInterfaceParameterKindsForInst sp inst
  let expectedKindPairs = zip (instParams inst) kinds
  subs <- forM expectedKindPairs (\(ity, iKind) -> do
    inferred <- inferKindOfTypeSafe sp ity
    case inferred of
      Left{} -> halt $ KindError (Just sp) $
                "Could not infer a kind for " <> prettyQuoted ity
      Right tyKind -> do
        eqres <- equalKinds sp iKind tyKind
        case eqres of
          Right pf -> pure $ equalityProofSubstitution pf
          Left{} -> illKindedNEq sp iKind tyKind)
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
kindCheckConstr :: (?globals :: Globals) => Span -> TConstraint -> MaybeT Checker ()
kindCheckConstr s ty = do
  case instFromTy ty of
    -- interface constraint
    Just inst -> kindCheckConstraint s inst >> pure ()
    -- predicate
    Nothing -> do
      kind <- inferKindOfType s ty
      case kind of
        KConstraint Predicate -> pure ()
        _ -> illKindedNEq s (KConstraint Predicate) kind


-- | Kind-check a type scheme.
-- |
-- | We expect a type scheme to have kind 'KType'.
kindCheckSig :: (?globals :: Globals) => Span -> TypeScheme -> MaybeT Checker ()
kindCheckSig s tys@(Forall _ quantifiedVariables constraints ty) = inTysContext $ do
  -- first, verify all the constraints are well-kinded
  mapM_ (kindCheckConstr s) constraints

  kind <- inferKindOfType s ty
  case kind of
    KType -> pure ()
    KPromote (TyCon k) | internalName k == "Protocol" -> pure ()
    _     -> illKindedNEq s KType kind
  where inTysContext = withBindings quantifiedVariables ForallQ


-----------------------
-- Predicate Helpers --
-----------------------


compileAndAddPredicate :: (?globals :: Globals) => Span -> Type -> MaybeT Checker ()
compileAndAddPredicate sp ty =
  compileTypeConstraintToConstraint sp ty >>= addPredicate


-- | Constrain the typescheme with the given predicates.
constrainTysWithPredicates :: (?globals :: Globals) => [Type] -> TypeScheme -> TypeScheme
constrainTysWithPredicates preds (Forall sp binds constrs ty) = Forall sp binds (constrs <> preds) ty


----------------------------
-- Type-inference Helpers --
----------------------------


-- | Given a set of (parameter kind, parameter type) pairs, attempt to
-- | map free variables in the types to appropriate kinds.
getParamsFreeVarKinds :: (?globals :: Globals) => Span -> [(Kind, Type)] -> MaybeT Checker [(Id, Kind)]
getParamsFreeVarKinds sp = fmap (tyMapVars . snd) . getParamsKinds'
  where
    -- | Assigns a kind to each component of the type.
    getParamsKinds' :: [(Kind, Type)] -> MaybeT Checker (Substitution, [(Type, Kind)])
    getParamsKinds' kts = do
      (subs, fvks) <- fmap unzip $ mapM (uncurry getParamKinds) kts
      sub <- either (conflictingKinds sp) pure =<< combineManySubstitutionsSafe sp subs
      fvks' <- instantiateKinds sub (concat fvks) >>= simplifyBindings
      pure (sub, fvks')
    getParamKinds :: Kind -> Type -> MaybeT Checker (Substitution, [(Type, Kind)])
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
             tvc <- getTyVarContext
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
    getCoeffectFreeVarKinds :: Coeffect -> MaybeT Checker (Substitution, [(Type, Kind)])
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

    zipKindVars :: Id -> Kind -> Kind -> MaybeT Checker (Either FailedCombination Substitution)
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

    instantiateKind :: (Id, Kind) -> [(Type, Kind)] -> MaybeT Checker [(Type, Kind)]
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
    (<*->) :: (Semigroup a) => MaybeT Checker (Substitution, a) -> MaybeT Checker (Substitution, a) -> MaybeT Checker (Substitution, a)
    (<*->) m n = do
      (sub1, r1) <- m
      (sub2, r2) <- n
      sub <- combineSubstitutionsSafe sp sub1 sub2
      case sub of
        Left e -> conflictingKinds sp e
        Right sub -> pure (sub, r1 <> r2)


conflictingKinds :: (?globals :: Globals) => Span -> (Id, Substitutors, Substitutors) -> MaybeT Checker a
conflictingKinds sp (v, k, k2) = halt $ KindError (Just sp) $
  concat [ prettyQuoted v, " cannot have both kind "
         , prettyQuotedS k, " and kind ", prettyQuotedS k2 ]
  where prettyQuotedS (SubstT t) = prettyQuoted t
        prettyQuotedS (SubstK k) = prettyQuoted k
        prettyQuotedS (SubstC c) = prettyQuoted c
        prettyQuotedS (SubstE e) = prettyQuoted e
