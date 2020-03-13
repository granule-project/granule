{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Checker where

import Control.Arrow (second)
import Control.Monad (unless)
import Control.Monad.State.Strict
import Control.Monad.Except (throwError)
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.Split (splitPlaces)
import qualified Data.List.NonEmpty as NonEmpty (toList)
import Data.Maybe
import qualified Data.Text as T

import Language.Granule.Checker.CoeffectsTypeConverter
import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Coeffects
import Language.Granule.Checker.Effects
import Language.Granule.Checker.Constraints
import Language.Granule.Checker.Kinds
import Language.Granule.Checker.KindsImplicit
import Language.Granule.Checker.Exhaustivity
import Language.Granule.Checker.Monad
import Language.Granule.Checker.NameClash
import Language.Granule.Checker.Patterns
import Language.Granule.Checker.Predicates
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Checker.Simplifier
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.Types
import Language.Granule.Checker.Variables
import Language.Granule.Context

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Helpers (freeVars, hasHole)
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pattern (Pattern(..))
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Synthesis.Splitting

import Language.Granule.Utils

--import Debug.Trace

-- Checking (top-level)
check :: (?globals :: Globals)
  => AST () ()
  -> IO (Either (NonEmpty CheckerError) (AST () Type))
check ast@(AST dataDecls defs imports hidden name) =
  evalChecker (initState { allHiddenNames = hidden }) $ (do
      _    <- checkNameClashes ast
      _    <- runAll checkTyCon (Primitives.dataTypes ++ dataDecls)
      _    <- runAll checkDataCons (Primitives.dataTypes ++ dataDecls)
      defs <- runAll kindCheckDef defs
      let defCtxt = map (\(Def _ name _ _ tys) -> (name, tys)) defs
      defs <- runAll (checkDef defCtxt) defs
      pure $ AST dataDecls defs imports hidden name)

-- Synthing the type of a single expression in the context of an asy
synthExprInIsolation :: (?globals :: Globals)
  => AST () ()
  -> Expr () ()
  -> IO (Either (NonEmpty CheckerError) (Either TypeScheme Kind))
synthExprInIsolation ast@(AST dataDecls defs imports hidden name) expr =
  evalChecker (initState { allHiddenNames = hidden }) $ do
      _    <- checkNameClashes ast
      _    <- runAll checkTyCon (Primitives.dataTypes ++ dataDecls)
      _    <- runAll checkDataCons (Primitives.dataTypes ++ dataDecls)
      defs <- runAll kindCheckDef defs
      let defCtxt = map (\(Def _ name _ _ tys) -> (name, tys)) defs
      -- Since we need to return a type scheme, have a look first
      -- for top-level identifiers with their schemes
      case expr of
        -- Lookup in data constructors
        (Val s _ _ (Constr _ c [])) -> do
          mConstructor <- lookupDataConstructor s c
          case mConstructor of
            Just (tySch, _) -> return $ Left tySch
            Nothing -> do
              st <- get
              -- Or see if this is a kind constructors
              case lookup c (typeConstructors st) of
                Just (k, _, _) -> return $ Right k
                Nothing -> throw UnboundDataConstructor{ errLoc = s, errId = c }

        -- Lookup in definitions
        (Val s _ _ (Var _ x)) -> do
          case lookup x (defCtxt <> Primitives.builtins) of
            Just tyScheme -> return $ Left tyScheme
            Nothing -> throw UnboundVariableError{ errLoc = s, errId = x }

        -- Otherwise, do synth
        _ -> do
          (ty, _, _, _) <- synthExpr defCtxt [] Positive expr
          return $ Left $ Forall nullSpanNoFile [] [] ty

-- TODO: we are checking for name clashes again here. Where is the best place
-- to do this check?
checkTyCon :: DataDecl -> Checker ()
checkTyCon d@(DataDecl sp name tyVars kindAnn ds)
  = lookup name <$> gets typeConstructors >>= \case
    Just _ -> throw TypeConstructorNameClash{ errLoc = sp, errId = name }
    Nothing -> modify' $ \st ->
      st{ typeConstructors = (name, (tyConKind, ids, isIndexedDataType d)) : typeConstructors st }
  where
    ids = map dataConstrId ds -- the IDs of data constructors
    tyConKind = mkKind (map snd tyVars)
    mkKind [] = case kindAnn of Just k -> k; Nothing -> KType -- default to `Type`
    mkKind (v:vs) = KFun v (mkKind vs)

checkDataCons :: (?globals :: Globals) => DataDecl -> Checker ()
checkDataCons (DataDecl sp name tyVars k dataConstrs) = do
    st <- get
    let kind = case lookup name (typeConstructors st) of
                Just (kind,_,_) -> kind
                Nothing -> error $ "Internal error. Trying to lookup data constructor " <> pretty name
    modify' $ \st -> st { tyVarContext = [(v, (k, ForallQ)) | (v, k) <- tyVars] }
    mapM_ (checkDataCon name kind tyVars) dataConstrs

checkDataCon :: (?globals :: Globals)
  => Id -- ^ The type constructor and associated type to check against
  -> Kind -- ^ The kind of the type constructor
  -> Ctxt Kind -- ^ The type variables
  -> DataConstr -- ^ The data constructor to check
  -> Checker () -- ^ Return @Just ()@ on success, @Nothing@ on failure
checkDataCon
  tName
  kind
  tyVarsT
  d@(DataConstrIndexed sp dName tySch@(Forall s tyVarsD constraints ty)) = do
    case map fst $ intersectCtxts tyVarsT tyVarsD of
      [] -> do -- no clashes

        -- Only relevant type variables get included
        let tyVars = relevantSubCtxt (freeVars ty) (tyVarsT <> tyVarsD)
        let tyVars_justD = relevantSubCtxt (freeVars ty) tyVarsD

        -- Add the type variables from the data constructor into the environment
        modify $ \st -> st { tyVarContext =
               [(v, (k, ForallQ)) | (v, k) <- tyVars_justD] ++ tyVarContext st }
        tySchKind <- inferKindOfTypeInContext sp tyVars ty

        -- Freshen the data type constructors type
        (ty, tyVarsFreshD, substFromFreshening, constraints, []) <-
             freshPolymorphicInstance ForallQ False (Forall s tyVars constraints ty) []

        -- Create a version of the data constructor that matches the data type head
        -- but with a list of coercions

        ixKinds <- mapM (substitute substFromFreshening) (indexKinds kind)
        (ty', coercions, tyVarsNewAndOld) <- checkAndGenerateSubstitution sp tName ty ixKinds

        -- Reconstruct the data constructor's new type scheme
        let tyVarsD' = tyVarsFreshD <> tyVarsNewAndOld
        let tySch = Forall sp tyVarsD' constraints ty'

        case tySchKind of
          KType ->
            registerDataConstructor tySch coercions

          KPromote (TyCon k) | internalName k == "Protocol" ->
            registerDataConstructor tySch coercions

          _ -> throw KindMismatch{ errLoc = sp, tyActualK = Just ty, kExpected = KType, kActual = kind }

      (v:vs) -> (throwError . fmap mkTyVarNameClashErr) (v:|vs)
  where
    indexKinds (KFun k1 k2) = k1 : indexKinds k2
    indexKinds k = []

    registerDataConstructor dataConstrTy subst = do
      st <- get
      case extend (dataConstructors st) dName (dataConstrTy, subst) of
        Just ds -> put st { dataConstructors = ds, tyVarContext = [] }
        Nothing -> throw DataConstructorNameClashError{ errLoc = sp, errId = dName }

    mkTyVarNameClashErr v = DataConstructorTypeVariableNameClash
        { errLoc = sp
        , errDataConstructorId = dName
        , errTypeConstructor = tName
        , errVar = v
        }

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
       Span                     -- ^ Location of this application
    -> Id                       -- ^ Name of the type constructor
    -> Type                     -- ^ Type of the data constructor
    -> [Kind]                   -- ^ Types of the remaining data type indices
    -> Checker (Type, Substitution, Ctxt Kind)
checkAndGenerateSubstitution sp tName ty ixkinds =
    checkAndGenerateSubstitution' sp tName ty (reverse ixkinds)
  where
    checkAndGenerateSubstitution' sp tName (TyCon tC) []
        | tC == tName = return (TyCon tC, [], [])
        | otherwise = throw UnexpectedTypeConstructor
          { errLoc = sp, tyConActual = tC, tyConExpected = tName }

    checkAndGenerateSubstitution' sp tName (FunTy id arg res) kinds = do
      (res', subst, tyVarsNew) <- checkAndGenerateSubstitution' sp tName res kinds
      return (FunTy id arg res', subst, tyVarsNew)

    checkAndGenerateSubstitution' sp tName (TyApp fun arg) (kind:kinds) = do
      varSymb <- freshIdentifierBase "t"
      let var = mkId varSymb
      (fun', subst, tyVarsNew) <-  checkAndGenerateSubstitution' sp tName fun kinds
      return (TyApp fun' (TyVar var), (var, SubstT arg) : subst, (var, kind) : tyVarsNew)

    checkAndGenerateSubstitution' sp _ t _ =
      throw InvalidTypeDefinition { errLoc = sp, errTy = t }

checkDef :: (?globals :: Globals)
         => Ctxt TypeScheme  -- context of top-level definitions
         -> Def () ()        -- definition
         -> Checker (Def () Type)
checkDef defCtxt (Def s defName rf el@(EquationList _ _ _ equations) tys@(Forall s_t foralls constraints ty)) = do
    -- duplicate forall bindings
    case duplicates (map (sourceName . fst) foralls) of
      [] -> pure ()
      (d:ds) -> throwError $ fmap (DuplicateBindingError s_t) (d :| ds)

    -- Clean up knowledge shared between equations of a definition
    modify (\st -> st { guardPredicates = [[]]
                      , patternConsumption = initialisePatternConsumptions equations } )

    elaboratedEquations :: [Equation () Type] <- runAll elaborateEquation equations

    checkGuardsForImpossibility s defName
    checkGuardsForExhaustivity s defName ty equations
    let el' = el { equations = elaboratedEquations }
    pure $ Def s defName rf el' tys
  where
    elaborateEquation :: Equation () () -> Checker (Equation () Type)
    elaborateEquation equation = do
      -- Erase the solver predicate between equations
        modify' $ \st -> st
            { predicateStack = []
            , tyVarContext = []
            , guardContexts = []
            , uniqueVarIdCounterMap = mempty
            }
        elaboratedEq <- checkEquation defCtxt defName equation tys

        -- Solve the generated constraints
        checkerState <- get

        let predicate = Conj $ predicateStack checkerState
        solveConstraints predicate (getSpan equation) defName
        pure elaboratedEq

checkEquation :: (?globals :: Globals) =>
     Ctxt TypeScheme -- context of top-level definitions
  -> Id              -- Name of the definition
  -> Equation () ()  -- Equation
  -> TypeScheme      -- Type scheme
  -> Checker (Equation () Type)

checkEquation defCtxt id (Equation s () rf pats expr) tys@(Forall _ foralls constraints ty) = do
  -- Check that the lhs doesn't introduce any duplicate binders
  duplicateBinderCheck s pats

  -- Freshen the type context
  modify (\st -> st { tyVarContext = map (\(n, c) -> (n, (c, ForallQ))) foralls})

  -- Create conjunct to capture the pattern constraints
  newConjunct

  mapM_ (\ty -> do
    pred <- compileTypeConstraintToConstraint s ty
    addPredicate pred) constraints

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

  -- The type of the equation, after substitution.
  equationTy' <- substitute subst ty
  let equationTy'' = refineEquationTy patternGam equationTy'

  -- Store the equation type in the state in case it is needed when splitting
  -- on a hole.
  modify (\st -> st { equationTy = Just equationTy'' })

  patternGam <- substitute subst patternGam

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
      let elab = Equation s ty rf elaborated_pats elaboratedExpr

      elab' <- substitute subst'' elab
      return elab'

    -- Anything that was bound in the pattern but not used up
    (p:ps) -> illLinearityMismatch s (p:|ps)

  where
    -- Given a context and a function type, refines the type by deconstructing
    -- patterns into their constituent patterns and replacing parts of the type
    -- by the corresponding pattern.
    -- e.g. Given a pattern: Cons x xs
    --      and a type:      Vec (n+1) t -> Vec n t
    --      returns:         t -> Vec n t -> Vec n t
    refineEquationTy :: [(Id, Assumption)] -> Type -> Type
    refineEquationTy patternGam ty =
      case patternGam of
        [] -> ty
        (_:_) ->
          let patternArities = map patternArity pats
              patternFunTys = map (map assumptionToType) (splitPlaces patternArities patternGam)
          in replaceParameters patternFunTys ty

    -- Computes how many arguments a pattern has.
    -- e.g. Cons x xs --> 2
    patternArity :: Pattern a -> Integer
    patternArity (PBox _ _ _ p) = patternArity p
    patternArity (PConstr _ _ _ _ ps) = sum (map patternArity ps)
    patternArity _ = 1

    replaceParameters :: [[Type]] -> Type -> Type
    replaceParameters [] ty = ty
    replaceParameters ([]:tss) (FunTy id _ ty) = replaceParameters tss ty
    replaceParameters ((t:ts):tss) ty =
      FunTy Nothing t (replaceParameters (ts:tss) ty)
    replaceParameters _ t = error $ "Expecting function type: " <> pretty t

    -- Convert an id+assumption to a type.
    assumptionToType :: (Id, Assumption) -> Type
    assumptionToType (_, Linear t) = t
    assumptionToType (_, Discharged t _) = t

-- Polarities are used to understand when a type is
-- `expected` vs. `actual` (i.e., for error messages)
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

checkExpr :: (?globals :: Globals)
          => Ctxt TypeScheme   -- context of top-level definitions
          -> Ctxt Assumption   -- local typing context
          -> Polarity         -- polarity of <= constraints
          -> Bool             -- whether we are top-level or not
          -> Type             -- type
          -> Expr () ()       -- expression
          -> Checker (Ctxt Assumption, Substitution, Expr () Type)

-- Hit an unfilled hole
checkExpr _ ctxt _ _ t (Hole s _ _ vars) = do
  st <- get

  let getIdName (Id n _) = n
  let boundVariableIds = map fst $ filter (\ (id, _) -> getIdName id `elem` map getIdName vars) ctxt
  let holeCtxt = relevantSubCtxt boundVariableIds ctxt
  let unboundVariables = filter (\ x -> isNothing (lookup (getIdName x) (map (\ (Id a _, s) -> (a, s)) ctxt))) vars

  case unboundVariables of
    (v:_) -> throw UnboundVariableError{ errLoc = s, errId = v }
    [] -> do
      let snd3 (a, b, c) = b
      let pats = map (second snd3) (typeConstructors st)
      constructors <- mapM (\ (a, b) -> do
        dc <- mapM (lookupDataConstructor s) b
        let sd = zip (fromJust $ lookup a pats) (catMaybes dc)
        return (a, sd)) pats
      cases <- generateCases s constructors holeCtxt
      throw $ HoleMessage s t ctxt (tyVarContext st) cases

-- Checking of constants
checkExpr _ [] _ _ ty@(TyCon c) (Val s _ rf (NumInt n))   | internalName c == "Int" = do
    let elaborated = Val s ty rf (NumInt n)
    return ([], [], elaborated)

checkExpr _ [] _ _ ty@(TyCon c) (Val s _ rf (NumFloat n)) | internalName c == "Float" = do
    let elaborated = Val s ty rf (NumFloat n)
    return ([], [], elaborated)

-- Differentially private floats
checkExpr _ [] _ _ ty@(TyCon c) (Val s _ rf (NumFloat n)) | internalName c == "DFloat" = do
    let elaborated = Val s ty rf (NumFloat n)
    return ([], [], elaborated)

checkExpr defs gam pol _ ty@(FunTy _ sig tau) (Val s _ rf (Abs _ p t e)) = do
  -- If an explicit signature on the lambda was given, then check
  -- it confirms with the type being checked here

  (tau', subst1) <- case t of
    Nothing -> return (tau, [])
    Just t' -> do
      (eqT, unifiedType, subst) <- equalTypes s sig t'
      unless eqT $ throw TypeError{ errLoc = s, tyExpected = sig, tyActual = t' }
      return (tau, subst)

  newConjunct

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
          ctxtApprox s (gam' `intersectCtxts` bindings) bindings

          concludeImplication s localVars

          let elaborated = Val s ty rf (Abs ty elaboratedP t elaboratedE)

          return (gam' `subtractCtxt` bindings, subst, elaborated)

       (p:ps) -> illLinearityMismatch s (p:|ps)
  else throw RefutablePatternError{ errLoc = s, errPat = p }

-- Application special case for built-in 'scale'
-- TODO: needs more thought
checkExpr defs gam pol topLevel tau
          (App s _ rf (App s' _ rf' (Val s'' _ rf'' (Var _ v)) (Val s3 _ rf3 (NumFloat x))) e) | internalName v == "scale" = do

    let floatTy = TyCon $ mkId "DFloat"

    (eq, _, subst) <- equalTypes s floatTy tau
    if eq then do
      -- Type check the argument
      (gam, subst', elab) <- checkExpr defs gam pol topLevel (Box (CFloat (toRational x)) floatTy) e

      subst'' <- combineSubstitutions s subst subst'

      -- Create elborated AST
      let scaleTy = FunTy Nothing floatTy (FunTy Nothing (Box (CFloat (toRational x)) floatTy) floatTy)
      let elab' = App s floatTy rf
                    (App s' scaleTy rf' (Val s'' floatTy rf'' (Var floatTy v)) (Val s3 floatTy rf3 (NumFloat x))) elab

      return (gam, subst'', elab')
      else
        throw $ TypeError { errLoc = s, tyExpected = TyCon $ mkId "DFloat", tyActual = tau }

-- Application checking
checkExpr defs gam pol topLevel tau (App s _ rf e1 e2) = do
    (argTy, gam2, subst2, elaboratedR) <- synthExpr defs gam pol e2

    funTy <- substitute subst2 (FunTy Nothing argTy tau)
    (gam1, subst1, elaboratedL) <- checkExpr defs gam pol topLevel funTy e1

    gam <- ctxtPlus s gam1 gam2

    subst <- combineSubstitutions s subst1 subst2

    let elaborated = App s tau rf elaboratedL elaboratedR
    return (gam, subst, elaborated)

{-

[G] |- e : t
 ---------------------
[G]*r |- [e] : []_r t

-}

-- Promotion
checkExpr defs gam pol _ ty@(Box demand tau) (Val s _ rf (Promote _ e)) = do
    let vars =
          if hasHole e
            -- If we are promoting soemthing with a hole, then put all free variables in scope
            then map fst gam
            -- Otherwise we need to discharge only things that get used
            else freeVars e

    (gam', subst, elaboratedE) <- checkExpr defs gam pol False tau e

    -- Causes a promotion of any typing assumptions that came from variable
    -- inside a guard from an enclosing case that have kind Level
    -- This prevents control-flow attacks and is a special case for Level
    -- (the guard contexts come from a special context in the solver)
    guardGam <- allGuardContexts
    guardGam' <- filterM isLevelKinded guardGam
    gam'' <- multAll s (vars <> map fst guardGam') demand (gam' <> guardGam')

    let elaborated = Val s ty rf (Promote tau elaboratedE)
    return (gam'', subst, elaborated)
  where
    -- Calculate whether a type assumption is level kinded
    isLevelKinded (_, as) = do
        -- TODO: should deal with the subst
        (ty, _) <- inferCoeffectTypeAssumption s as
        return $ case ty of
          Just (TyCon (internalName -> "Level"))
            -> True
          Just (TyApp (TyCon (internalName -> "Interval"))
                      (TyCon (internalName -> "Level")))
            -> True
          _ -> False

-- Check a case expression
checkExpr defs gam pol True tau (Case s _ rf guardExpr cases) = do

  -- Synthesise the type of the guardExpr
  (guardTy, guardGam, substG, elaboratedGuard) <- synthExpr defs gam pol guardExpr
  pushGuardContext guardGam

  -- Dependent / GADT pattern matches not allowed in a case
  ixed <- isIndexedType guardTy
  when ixed (throw $ CaseOnIndexedType s guardTy)

  newCaseFrame

  -- Check each of the branches
  branchCtxtsAndSubst <-
    forM cases $ \(pat_i, e_i) -> do

      -- Build the binding context for the branch pattern
      newConjunct
      (patternGam, eVars, subst, elaborated_pat_i, _) <- ctxtFromTypedPattern s guardTy pat_i NotFull
      newConjunct

      -- Checking the case body
      (localGam, subst', elaborated_i) <- checkExpr defs (patternGam <> gam) pol False tau e_i

      -- Check that the use of locally bound variables matches their bound type
      ctxtApprox s (localGam `intersectCtxts` patternGam) patternGam

      -- Conclude the implication
      concludeImplication (getSpan pat_i) eVars

      -- Check linear use in anything Linear
      gamSoFar <- ctxtPlus s guardGam localGam
      case checkLinearity patternGam gamSoFar of
        -- Return the resulting computed context, without any of
        -- the variable bound in the pattern of this branch
        [] -> do
           return (localGam `subtractCtxt` patternGam
                 , subst'
                 , (elaborated_pat_i, elaborated_i))

        -- Anything that was bound in the pattern but not used correctly
        p:ps -> illLinearityMismatch s (p:|ps)

  -- All branches must be possible
  checkGuardsForImpossibility s $ mkId "case"

  -- Pop from stacks related to case
  _ <- popGuardContext
  popCaseFrame

  -- Find the upper-bound of the contexts
  let (branchCtxts, substs, elaboratedCases) = unzip3 branchCtxtsAndSubst
  (branchesGam, tyVars) <- foldM (\(ctxt, vars) ctxt' -> do
    (ctxt'', vars') <- joinCtxts s ctxt ctxt'
    return (ctxt'', vars ++ vars')) (head branchCtxts, []) (tail branchCtxts)

  -- Contract the outgoing context of the guard and the branches (joined)
  g <- ctxtPlus s branchesGam guardGam

  subst <- combineManySubstitutions s (substG : substs)

  -- Exisentially quantify any ty variables generated by joining contexts
  mapM_ (uncurry existential) tyVars

  let elaborated = Case s tau rf elaboratedGuard elaboratedCases
  return (g, subst, elaborated)

-- All other expressions must be checked using synthesis
checkExpr defs gam pol topLevel tau e = do

  (tau', gam', subst', elaboratedE) <- synthExpr defs gam pol e

  -- Now to do a type equality on check type `tau` and synth type `tau'`
  (tyEq, _, subst) <-
        if topLevel
          -- If we are checking a top-level, then don't allow overapproximation
          then do
            debugM "** Compare for equality " $ pretty tau' <> " = " <> pretty tau
            equalTypesWithPolarity (getSpan e) SndIsSpec tau' tau
          else do
            debugM "** Compare for equality " $ pretty tau' <> " :> " <> pretty tau
            lEqualTypesWithPolarity (getSpan e) SndIsSpec tau' tau

  if tyEq
    then do
      substFinal <- combineSubstitutions (getSpan e) subst subst'
      return (gam', substFinal, elaboratedE)
    else do
      case pol of
        Positive -> throw TypeError{ errLoc = getSpan e, tyExpected = tau , tyActual = tau' }
        Negative -> throw TypeError{ errLoc = getSpan e, tyExpected = tau', tyActual =  tau }

-- | Synthesise the 'Type' of expressions.
-- See <https://en.wikipedia.org/w/index.php?title=Bidirectional_type_checking&redirect=no>
synthExpr :: (?globals :: Globals)
          => Ctxt TypeScheme   -- ^ Context of top-level definitions
          -> Ctxt Assumption   -- ^ Local typing context
          -> Polarity          -- ^ Polarity of subgrading
          -> Expr () ()        -- ^ Expression
          -> Checker (Type, Ctxt Assumption, Substitution, Expr () Type)

-- Hit an unfilled hole
synthExpr _ ctxt _ (Hole s _ _ _) = throw $ InvalidHolePosition s

-- Literals can have their type easily synthesised
synthExpr _ _ _ (Val s _ rf (NumInt n))  = do
  let t = TyCon $ mkId "Int"
  return (t, [], [], Val s t rf (NumInt n))

synthExpr _ _ _ (Val s _ rf (NumFloat n)) = do
  let t = TyCon $ mkId "Float"
  return (t, [], [], Val s t rf (NumFloat n))

synthExpr _ _ _ (Val s _ rf (CharLiteral c)) = do
  let t = TyCon $ mkId "Char"
  return (t, [], [], Val s t rf (CharLiteral c))

synthExpr _ _ _ (Val s _ rf (StringLiteral c)) = do
  let t = TyCon $ mkId "String"
  return (t, [], [], Val s t rf (StringLiteral c))

-- Secret syntactic weakening
synthExpr defs gam pol
  (App s _ _ (Val _ _ _ (Var _ (sourceName -> "weak__"))) v@(Val _ _ _ (Var _ x))) = do

  (t, _, subst, elabE) <- synthExpr defs gam pol v

  return (t, [(x, Discharged t (CZero (TyCon $ mkId "Level")))], subst, elabE)

-- Constructors
synthExpr _ gam _ (Val s _ rf (Constr _ c [])) = do
  -- Should be provided in the type checkers environment
  st <- get
  mConstructor <- lookupDataConstructor s c
  case mConstructor of
    Just (tySch, coercions) -> do
      -- Freshen the constructor
      -- (discarding any fresh type variables, info not needed here)

      (ty, _, _, constraints, coercions') <- freshPolymorphicInstance InstanceQ False tySch coercions

      mapM_ (\ty -> do
        pred <- compileTypeConstraintToConstraint s ty
        addPredicate pred) constraints

      -- Apply coercions
      ty <- substitute coercions' ty

      let elaborated = Val s ty rf (Constr ty c [])
      return (ty, [], [], elaborated)

    Nothing -> throw UnboundDataConstructor{ errLoc = s, errId = c }

-- Case synthesis
synthExpr defs gam pol (Case s _ rf guardExpr cases) = do
  -- Synthesise the type of the guardExpr
  (guardTy, guardGam, substG, elaboratedGuard) <- synthExpr defs gam pol guardExpr
  -- then synthesise the types of the branches

  -- Dependent / GADT pattern matches not allowed in a case
  ixed <- isIndexedType guardTy
  when ixed (throw $ CaseOnIndexedType s guardTy)

  newCaseFrame

  branchTysAndCtxtsAndSubsts <-
    forM cases $ \(pati, ei) -> do
      -- Build the binding context for the branch pattern
      newConjunct
      (patternGam, eVars, subst, elaborated_pat_i, _) <- ctxtFromTypedPattern s guardTy pati NotFull
      newConjunct

      -- Synth the case body
      (tyCase, localGam, subst', elaborated_i) <- synthExpr defs (patternGam <> gam) pol ei

      -- Check that the use of locally bound variables matches their bound type
      ctxtApprox s (localGam `intersectCtxts` patternGam) patternGam

      -- Conclude
      concludeImplication (getSpan pati) eVars

      -- Check linear use in this branch
      gamSoFar <- ctxtPlus s guardGam localGam
      case checkLinearity patternGam gamSoFar of
         -- Return the resulting computed context, without any of
         -- the variable bound in the pattern of this branch
         [] -> return (tyCase
                    , (localGam `subtractCtxt` patternGam, subst')
                    , (elaborated_pat_i, elaborated_i))
         p:ps -> illLinearityMismatch s (p:|ps)

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
  (branchesGam, tyVars) <- foldM (\(ctxt, vars) ctxt' -> do
    (ctxt'', vars') <- joinCtxts s ctxt ctxt'
    return (ctxt'', vars ++ vars')) (head branchCtxts, []) (tail branchCtxts)

  -- Contract the outgoing context of the guard and the branches (joined)
  gamNew <- ctxtPlus s branchesGam guardGam

  subst <- combineManySubstitutions s (substG : branchSubsts)

  -- Exisentially quantify any ty variables generated by joining contexts
  mapM_ (uncurry existential) tyVars

  let elaborated = Case s branchType rf elaboratedGuard elaboratedCases
  return (branchType, gamNew, subst, elaborated)

-- Diamond cut
-- let [[p]] <- [[e1 : sig]] in [[e2 : tau]]
synthExpr defs gam pol (LetDiamond s _ rf p optionalTySig e1 e2) = do
  (sig, gam1, subst1, elaborated1) <- synthExpr defs gam pol e1

  -- Check that a graded possibility type was inferred
  (ef1, ty1) <- case sig of
      Diamond ef1 ty1 -> return (ef1, ty1)
      t -> throw ExpectedEffectType{ errLoc = s, errTy = t }

  -- Type body of the let...
  -- ...in the context of the binders from the pattern
  (binders, _, substP, elaboratedP, _)  <- ctxtFromTypedPattern s ty1 p NotFull
  pIrrefutable <- isIrrefutable s ty1 p
  unless pIrrefutable $ throw RefutablePatternError{ errLoc = s, errPat = p }
  (tau, gam2, subst2, elaborated2) <- synthExpr defs (binders <> gam) pol e2

  -- Check that a graded possibility type was inferred
  (ef2, ty2) <- case tau of
      Diamond ef2 ty2 -> return (ef2, ty2)
      t -> throw ExpectedEffectType{ errLoc = s, errTy = t }

  optionalSigEquality s optionalTySig ty1

  -- Check that usage matches the binding grades/linearity
  -- (performs the linearity check)
  ctxtEquals s (gam2 `intersectCtxts` binders) binders

  gamNew <- ctxtPlus s (gam2 `subtractCtxt` binders) gam1

  (efTy, u) <- twoEqualEffectTypes s ef1 ef2
  -- Multiply the effects
  ef <- effectMult s efTy ef1 ef2
  let t = Diamond ef ty2

  subst <- combineManySubstitutions s [substP, subst1, subst2, u]
  -- Synth subst
  t' <- substitute substP t

  let elaborated = LetDiamond s t rf elaboratedP optionalTySig elaborated1 elaborated2
  return (t, gamNew, subst, elaborated)

-- Variables
synthExpr defs gam _ (Val s _ rf (Var _ x)) =
   -- Try the local context
   case lookup x gam of
     Nothing ->
       -- Try definitions in scope
       case lookup x (defs <> Primitives.builtins) of
         Just tyScheme  -> do
           (ty', _, _, constraints, []) <- freshPolymorphicInstance InstanceQ False tyScheme [] -- discard list of fresh type variables

           mapM_ (\ty -> do
             pred <- compileTypeConstraintToConstraint s ty
             addPredicate pred) constraints

           let elaborated = Val s ty' rf (Var ty' x)
           return (ty', [], [], elaborated)

         -- Couldn't find it
         Nothing -> throw UnboundVariableError{ errLoc = s, errId = x }

     -- In the local context
     Just (Linear ty)       -> do
       let elaborated = Val s ty rf (Var ty x)
       return (ty, [(x, Linear ty)], [], elaborated)

     Just (Discharged ty c) -> do
       (k, subst) <- inferCoeffectType s c
       let elaborated = Val s ty rf (Var ty x)
       return (ty, [(x, Discharged ty (COne k))], subst, elaborated)

-- Specialised application for scale
{- TODO: needs thought -}
synthExpr defs gam pol
      (App s _ rf (Val s' _ rf' (Var _ v)) (Val s'' _ rf'' (NumFloat r))) | internalName v == "scale" = do

  let floatTy = TyCon $ mkId "DFloat"

  let scaleTyApplied = FunTy Nothing (Box (CFloat (toRational r)) floatTy) floatTy
  let scaleTy = FunTy Nothing floatTy scaleTyApplied

  let elab = App s scaleTy rf (Val s' scaleTy rf' (Var scaleTy v)) (Val s'' floatTy rf'' (NumFloat r))

  return (scaleTyApplied, [], [], elab)

-- Application
synthExpr defs gam pol (App s _ rf e e') = do
    (fTy, gam1, subst1, elaboratedL) <- synthExpr defs gam pol e

    case fTy of
      -- Got a function type for the left-hand side of application
      (FunTy _ sig tau) -> do
         liftIO $ debugM "FunTy sig" $ pretty sig
         (gam2, subst2, elaboratedR) <- checkExpr defs gam (flipPol pol) False sig e'
         gamNew <- ctxtPlus s gam1 gam2

         subst <- combineSubstitutions s subst1 subst2

         -- Synth subst
         tau    <- substitute subst2 tau

         let elaborated = App s tau rf elaboratedL elaboratedR
         return (tau, gamNew, subst, elaborated)

      -- Not a function type
      t -> throw LhsOfApplicationNotAFunction{ errLoc = s, errTy = t }

{- Promotion

[G] |- e : t
 ---------------------
[G]*r |- [e] : []_r t

-}

synthExpr defs gam pol (Val s _ rf (Promote _ e)) = do
   debugM "Synthing a promotion of " $ pretty e

   -- Create a fresh kind variable for this coeffect
   vark <- freshIdentifierBase $ "kprom_[" <> pretty (startPos s) <> "]"
   -- remember this new kind variable in the kind environment
   modify (\st -> st { tyVarContext = (mkId vark, (KCoeffect, InstanceQ)) : tyVarContext st })

   -- Create a fresh coeffect variable for the coeffect of the promoted expression
   var <- freshTyVarInContext (mkId $ "prom_[" <> pretty (startPos s) <> "]") (KPromote $ TyVar $ mkId vark)

   (t, gam', subst, elaboratedE) <- synthExpr defs gam pol e

   let finalTy = Box (CVar var) t
   let elaborated = Val s finalTy rf (Promote t elaboratedE)

   gam'' <- multAll s (freeVars e) (CVar var) gam'
   return (finalTy, gam'', subst, elaborated)


-- BinOp
synthExpr defs gam pol (Binop s _ rf op e1 e2) = do
    (t1, gam1, subst1, elaboratedL) <- synthExpr defs gam pol e1
    (t2, gam2, subst2, elaboratedR) <- synthExpr defs gam pol e2
    -- Look through the list of operators (of which there might be
    -- multiple matching operators)
    returnType <-
      selectFirstByType t1 t2
      . NonEmpty.toList
      . Primitives.binaryOperators
      $ op
    gamOut <- ctxtPlus s gam1 gam2
    subst <- combineSubstitutions s subst1 subst2
    let elaborated = Binop s returnType rf op elaboratedL elaboratedR
    return (returnType, gamOut, subst, elaborated)

  where
    -- No matching type were found (meaning there is a type error)
    selectFirstByType t1 t2 [] = throw FailedOperatorResolution
        { errLoc = s, errOp = op, errTy = t1 .-> t2 .-> var "..." }

    selectFirstByType t1 t2 ((FunTy _ opt1 (FunTy _ opt2 resultTy)):ops) = do
      -- Attempt to use this typing
      (result, local) <- peekChecker $ do
         (eq1, _, _) <- equalTypes s t1 opt1
         (eq2, _, _) <- equalTypes s t2 opt2
         return (eq1 && eq2)
      -- If successful then return this local computation
      case result of
        Right True -> local >> return resultTy
        _          -> selectFirstByType t1 t2 ops

    selectFirstByType t1 t2 (_:ops) = selectFirstByType t1 t2 ops


-- Abstraction, can only synthesise the types of
-- lambda in Church style (explicit type)
synthExpr defs gam pol (Val s _ rf (Abs _ p (Just sig) e)) = do

  newConjunct

  (bindings, localVars, substP, elaboratedP, _) <- ctxtFromTypedPattern s sig p NotFull

  newConjunct

  pIrrefutable <- isIrrefutable s sig p
  if pIrrefutable then do
     (tau, gam'', subst, elaboratedE) <- synthExpr defs (bindings <> gam) pol e

     -- Locally we should have this property (as we are under a binder)
     ctxtApprox s (gam'' `intersectCtxts` bindings) bindings

     let finalTy = FunTy Nothing sig tau
     let elaborated = Val s finalTy rf (Abs finalTy elaboratedP (Just sig) elaboratedE)

     substFinal <- combineSubstitutions s substP subst
     finalTy' <- substitute substP finalTy

     concludeImplication s localVars

     return (finalTy', gam'' `subtractCtxt` bindings, substFinal, elaborated)

  else throw RefutablePatternError{ errLoc = s, errPat = p }

-- Abstraction, can only synthesise the types of
-- lambda in Church style (explicit type)
synthExpr defs gam pol (Val s _ rf (Abs _ p Nothing e)) = do

  newConjunct

  tyVar <- freshTyVarInContext (mkId "t") KType
  let sig = (TyVar tyVar)

  (bindings, localVars, substP, elaboratedP, _) <- ctxtFromTypedPattern s sig p NotFull

  newConjunct

  pIrrefutable <- isIrrefutable s sig p
  if pIrrefutable then do
     (tau, gam'', subst, elaboratedE) <- synthExpr defs (bindings <> gam) pol e

     -- Locally we should have this property (as we are under a binder)
     ctxtApprox s (gam'' `intersectCtxts` bindings) bindings

     let finalTy = FunTy Nothing sig tau
     let elaborated = Val s finalTy rf (Abs finalTy elaboratedP (Just sig) elaboratedE)
     finalTy' <- substitute substP finalTy

     concludeImplication s localVars

     subst <- combineSubstitutions s substP subst

     return (finalTy', gam'' `subtractCtxt` bindings, subst, elaborated)
  else throw RefutablePatternError{ errLoc = s, errPat = p }

synthExpr _ _ _ e =
  throw NeedTypeSignature{ errLoc = getSpan e, errExpr = e }

-- Check an optional type signature for equality against a type
optionalSigEquality :: (?globals :: Globals) => Span -> Maybe Type -> Type -> Checker ()
optionalSigEquality _ Nothing _ = pure ()
optionalSigEquality s (Just t) t' = do
  _ <- equalTypes s t' t
  pure ()

solveConstraints :: (?globals :: Globals) => Pred -> Span -> Id -> Checker ()
solveConstraints predicate s name = do

  -- Get the coeffect kind context and constraints
  checkerState <- get
  let ctxtCk  = tyVarContext checkerState
  coeffectVars <- justCoeffectTypesConverted s ctxtCk
  -- remove any variables bound already in the preciate
  coeffectVars <- return (coeffectVars `deleteVars` boundVars predicate)

  debugM "tyVarContext" (pretty $ tyVarContext checkerState)
  debugM "context into the solver" (pretty $ coeffectVars)
  debugM "Solver predicate" $ pretty predicate

  result <- liftIO $ provePredicate predicate coeffectVars
  case result of
    QED -> return ()
    NotValid msg -> do
      msg' <- rewriteMessage msg
      simplPred <- simplifyPred predicate

      -- try trivial unsats again
      let unsats' = trivialUnsatisfiableConstraints simplPred
      if not (null unsats')
        then mapM_ (\c -> throw GradingError{ errLoc = getSpan c, errConstraint = Neg c }) unsats'
        else
          if msg' == "is Falsifiable\n"
            then throw SolverErrorFalsifiableTheorem
              { errLoc = s, errDefId = name, errPred = simplPred }
            else throw SolverErrorCounterExample
              { errLoc = s, errDefId = name, errPred = simplPred }
    NotValidTrivial unsats ->
       mapM_ (\c -> throw GradingError{ errLoc = getSpan c, errConstraint = Neg c }) unsats
    Timeout ->
        throw SolverTimeout{ errLoc = s, errSolverTimeoutMillis = solverTimeoutMillis, errDefId = name, errContext = "grading", errPred = predicate }
    OtherSolverError msg -> throw SolverError{ errLoc = s, errMsg = msg }
    SolverProofError msg -> error msg

-- Rewrite an error message coming from the solver
rewriteMessage :: String -> Checker String
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

-- | `ctxtEquals ctxt1 ctxt2` checks if two contexts are equal
--   and the typical pattern is that `ctxt2` represents a specification
--   (i.e. input to checking) and `ctxt1` represents actually usage
ctxtApprox :: (?globals :: Globals) =>
    Span -> Ctxt Assumption -> Ctxt Assumption -> Checker ()
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
          -- TODO: deal with the subst here
          _ <- relateByAssumption s ApproximatedBy (id, ass1) (id, ass2)
          return id
        -- ... if not check to see if the missing variable is linear
        Nothing   ->
           case ass2 of
             -- Linear gets instantly reported
             Linear t -> illLinearityMismatch s . pure $ LinearNotUsed id
             -- Else, this could be due to weakening so see if this is allowed
             Discharged t c -> do
               -- TODO: deal with the subst here
               (kind, _) <- inferCoeffectType s c
               -- TODO: deal with the subst here
               _ <- relateByAssumption s ApproximatedBy (id, Discharged t (CZero kind)) (id, ass2)
               return id
  -- Last we sanity check, if there is anything in ctxt1 that is not in ctxt2
  -- then we have an issue!
  forM_ ctxt1 $ \(id, ass1) ->
    if (id `elem` intersection)
      then return ()
      else throw UnboundVariableError{ errLoc = s, errId = id }


-- | `ctxtEquals ctxt1 ctxt2` checks if two contexts are equal
--   and the typical pattern is that `ctxt2` represents a specification
--   (i.e. input to checking) and `ctxt1` represents actually usage
ctxtEquals :: (?globals :: Globals) =>
    Span -> Ctxt Assumption -> Ctxt Assumption -> Checker ()
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
          -- -- TODO: deal with the subst here
          _ <- relateByAssumption s Eq (id, ass1) (id, ass2)
          return id
        -- ... if not check to see if the missing variable is linear
        Nothing   ->
           case ass2 of
             -- Linear gets instantly reported
             Linear t -> illLinearityMismatch s . pure $ LinearNotUsed id
             -- Else, this could be due to weakening so see if this is allowed
             Discharged t c -> do
               -- TODO: deal with the subst here
               (kind, _) <- inferCoeffectType s c
               -- TODO: deal with the subst here
               _ <- relateByAssumption s Eq (id, Discharged t (CZero kind)) (id, ass2)
               return id
  -- Last we sanity check, if there is anything in ctxt1 that is not in ctxt2
  -- then we have an issue!
  forM_ ctxt1 $ \(id, ass1) ->
    if (id `elem` intersection)
      then return ()
      else throw UnboundVariableError{ errLoc = s, errId = id }

{- | Take the least-upper bound of two contexts.
     If one context contains a linear variable that is not present in
    the other, then the resulting context will not have this linear variable.
    Also return s a list of new type variable created to do the join. -}
joinCtxts :: (?globals :: Globals) => Span -> Ctxt Assumption -> Ctxt Assumption
  -> Checker (Ctxt Assumption, Ctxt Kind)
joinCtxts s ctxt1 ctxt2 = do
    -- All the type assumptions from ctxt1 whose variables appear in ctxt2
    -- and weaken all others
    ctxt  <- intersectCtxtsWithWeaken s ctxt1 ctxt2
    -- All the type assumptions from ctxt2 whose variables appear in ctxt1
    -- and weaken all others
    ctxt' <- intersectCtxtsWithWeaken s ctxt2 ctxt1

    -- Make an context with fresh coeffect variables for all
    -- the variables which are in both ctxt1 and ctxt2...
    (varCtxt, tyVars) <- freshVarsIn s (map fst ctxt) ctxt

    -- ... and make these fresh coeffects the upper-bound of the coeffects
    -- in ctxt and ctxt'
    _ <- zipWith3M_ (relateByLUB s) ctxt ctxt' varCtxt
    -- Return the common upper-bound context of ctxt1 and ctxt2
    return (varCtxt, tyVars)
  where
    zipWith3M_ :: Monad m => (a -> b -> c -> m d) -> [a] -> [b] -> [c] -> m [d]
    zipWith3M_ f _ _ [] = return []
    zipWith3M_ f _ [] _ = return []
    zipWith3M_ f [] _ _ = return []
    zipWith3M_ f (x:xs) (y:ys) (z:zs) = do
      w <- f x y z
      ws <- zipWith3M_ f xs ys zs
      return $ w : ws

{- |  intersect contexts and weaken anything not appear in both
        relative to the left context (this is not commutative) -}
intersectCtxtsWithWeaken
  :: (?globals :: Globals)
  => Span
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Checker (Ctxt Assumption)
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

   weaken :: (Id, Assumption) -> Checker (Id, Assumption)
   weaken (var, Linear t) =
       return (var, Linear t)
   weaken (var, Discharged t c) = do
        -- TODO: deal with the subst here
       (kind, _) <- inferCoeffectType s c
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

-- Assumption that the two assumps are for the same variable
relateByAssumption :: (?globals :: Globals)
  => Span
  -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
  -> (Id, Assumption)
  -> (Id, Assumption)
  -> Checker Substitution

-- Linear assumptions ignored
relateByAssumption _ _ (_, Linear _) (_, Linear _) = return []

-- Discharged coeffect assumptions
relateByAssumption s rel (_, Discharged _ c1) (_, Discharged _ c2) = do
  (kind, subst, (inj1, inj2)) <- mguCoeffectTypesFromCoeffects s c1 c2
  addConstraint (rel s (inj1 c1) (inj2 c2) kind)
  return subst

-- Linear binding and a graded binding (likely from a promotion)
relateByAssumption s _ (idX, _) (idY, _) =
  if idX == idY
    then throw UnifyGradedLinear{ errLoc = s, errLinearOrGraded = idX }
    else error $ "Internal bug: " <> pretty idX <> " does not match " <> pretty idY

-- Relate 3 assumptions by the least-upper bound relation, i.e.,
--   `relateByLUB s c1 c2 c3` means `c3` is the lub of `c1` and `c2`
-- Assumption that the three assumptions are for the same variable
relateByLUB :: (?globals :: Globals)
  => Span
  -> (Id, Assumption)
  -> (Id, Assumption)
  -> (Id, Assumption)
  -> Checker Substitution

-- Linear assumptions ignored
relateByLUB _ (_, Linear _) (_, Linear _) (_, Linear _) = return []

-- Discharged coeffect assumptions
relateByLUB s (_, Discharged _ c1) (_, Discharged _ c2) (_, Discharged _ c3) = do
  (kind, subst, (inj1, inj2)) <- mguCoeffectTypesFromCoeffects s c1 c2
  addConstraint (Lub s (inj1 c1) (inj2 c2) c3 kind)
  return subst

-- Linear binding and a graded binding (likely from a promotion)
relateByLUB s (idX, _) (idY, _) (_, _) =
  if idX == idY
    then throw UnifyGradedLinear{ errLoc = s, errLinearOrGraded = idX }
    else error $ "Internal bug: " <> pretty idX <> " does not match " <> pretty idY

-- `freshVarsIn names ctxt` creates a new context with
-- all the variables names in `ctxt` that appear in the list
-- `vars` and are discharged are
-- turned into discharged coeffect assumptions annotated
-- with a fresh coeffect variable (and all variables not in
-- `vars` get deleted).
-- Returns also the list of newly generated type variables
-- e.g.
--  `freshVarsIn ["x", "y"] [("x", Discharged (2, Int),
--                           ("y", Linear Int),
--                           ("z", Discharged (3, Int)]
--  -> ([("x", Discharged (c5 :: Nat, Int),
--      ("y", Linear Int)]
--     , [c5 :: Nat])
freshVarsIn :: (?globals :: Globals) => Span -> [Id] -> (Ctxt Assumption)
            -> Checker (Ctxt Assumption, Ctxt Kind)
freshVarsIn s vars ctxt = do
    newCtxtAndTyVars <- mapM toFreshVar (relevantSubCtxt vars ctxt)
    let (newCtxt, tyVars) = unzip newCtxtAndTyVars
    return (newCtxt, catMaybes tyVars)
  where
    toFreshVar :: (Id, Assumption) -> Checker ((Id, Assumption), Maybe (Id, Kind))
    toFreshVar (var, Discharged t c) = do
      -- TODO: deal with the subst here
      (ctype, _) <- inferCoeffectType s c
      -- Create a fresh variable
      freshName <- freshIdentifierBase (internalName var)
      let cvar = mkId freshName
      -- Update the coeffect kind context
      modify (\s -> s { tyVarContext = (cvar, (promoteTypeToKind ctype, InstanceQ)) : tyVarContext s })

      -- Return the freshened var-type mapping
      -- and the new type variable
      return ((var, Discharged t (CVar cvar)), Just (cvar, promoteTypeToKind ctype))

    toFreshVar (var, Linear t) = return ((var, Linear t), Nothing)


-- Combine two contexts
ctxtPlus :: (?globals :: Globals) => Span -> Ctxt Assumption -> Ctxt Assumption
  -> Checker (Ctxt Assumption)
ctxtPlus _ [] ctxt2 = return ctxt2
ctxtPlus s ((i, v) : ctxt1) ctxt2 = do
  ctxt' <- extCtxt s ctxt2 i v
  ctxtPlus s ctxt1 ctxt'

-- ExtCtxt the context
extCtxt :: (?globals :: Globals) => Span -> Ctxt Assumption -> Id -> Assumption
  -> Checker (Ctxt Assumption)
extCtxt s ctxt var (Linear t) = do

  case lookup var ctxt of
    Just (Linear t') ->
       if t == t'
        then throw LinearityError{ errLoc = s, linearityMismatch = LinearUsedMoreThanOnce var }
        else throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = t' }
    Just (Discharged t' c) ->
       if t == t'
         then do
           -- TODO: deal with the subst here
           (k, _) <- inferCoeffectType s c
           return $ replace ctxt var (Discharged t (c `CPlus` COne k))
         else throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = t' }
    Nothing -> return $ (var, Linear t) : ctxt

extCtxt s ctxt var (Discharged t c) = do

  case lookup var ctxt of
    Just (Discharged t' c') ->
        if t == t'
        then return $ replace ctxt var (Discharged t' (c `CPlus` c'))
        else throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = t' }
    Just (Linear t') ->
        if t == t'
        then do
           -- TODO: deal with the subst here
           (k, _) <- inferCoeffectType s c
           return $ replace ctxt var (Discharged t (c `CPlus` COne k))
        else throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = t' }
    Nothing -> return $ (var, Discharged t c) : ctxt

-- Helper, foldM on a list with at least one element
fold1M :: Monad m => (a -> a -> m a) -> [a] -> m a
fold1M _ []     = error "Must have at least one case"
fold1M f (x:xs) = foldM f x xs

justLinear :: [(a, Assumption)] -> [(a, Assumption)]
justLinear [] = []
justLinear ((x, Linear t) : xs) = (x, Linear t) : justLinear xs
justLinear ((x, _) : xs) = justLinear xs

checkGuardsForExhaustivity :: (?globals :: Globals)
  => Span -> Id -> Type -> [Equation () ()] -> Checker ()
checkGuardsForExhaustivity s name ty eqs = do
  debugM "Guard exhaustivity" "todo"
  return ()

checkGuardsForImpossibility :: (?globals :: Globals) => Span -> Id -> Checker ()
checkGuardsForImpossibility s name = do
  -- Get top of guard predicate stack
  st <- get
  let ps = head $ guardPredicates st

  -- Convert all universal variables to existential
  tyVars <- tyVarContextExistential >>= justCoeffectTypesConverted s

  -- For each guard predicate
  forM_ ps $ \((ctxt, p), s) -> do

    -- Existentially quantify those variables occuring in the pattern in scope
    let thm = foldr (uncurry Exists) p ctxt

    debugM "impossibility" $ "about to try" <> pretty thm
    -- Try to prove the theorem
    result <- liftIO $ provePredicate thm tyVars

    p <- simplifyPred thm

    case result of
      QED -> return ()

      -- Various kinds of error
      -- TODO make errors better
      NotValid msg -> throw ImpossiblePatternMatch
        { errLoc = s
        , errId = name
        , errPred = p
        }
      NotValidTrivial unsats -> throw ImpossiblePatternMatchTrivial
        { errLoc = s
        , errId = name
        , errUnsats = unsats
        }
      Timeout -> throw SolverTimeout
        { errLoc = s
        , errDefId = name
        , errSolverTimeoutMillis = solverTimeoutMillis
        , errContext = "pattern match of an equation"
        , errPred = p
        }

      OtherSolverError msg -> throw ImpossiblePatternMatch
        { errLoc = s
        , errId = name
        , errPred = p
        }

      SolverProofError msg -> error msg
