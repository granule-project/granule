module Language.Granule.Synthesis.Splitting (generateCases) where

import Control.Arrow (second)
import Control.Monad.State.Strict (get, liftIO)
import Data.List (partition)
import Data.Maybe (fromJust, fromMaybe, isJust, mapMaybe, catMaybes)

import Language.Granule.Checker.CoeffectsTypeConverter
import Language.Granule.Checker.Constraints
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Patterns
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Variables

import Language.Granule.Context

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Utils

-- Generates a set of valid cases given a type and context of assumptions, in
-- the form of a pair of identifiers and lists of lists of patterns
-- which correspond to those identifiers.
generateCases :: (?globals :: Globals)
  => Span
  -> Ctxt (Ctxt (TypeScheme, Substitution))
  -> Ctxt Assumption
  -> Checker ([Id], [([Pattern ()], Ctxt Assumption)])
generateCases span constructors ctxt = do
  -- Determines whether an assumption should be treated as linear.
  let isLinear (_, a) =
        case a of
          Discharged _ _   -> False
          Linear (Box _ _) -> False
          Linear _         -> True
  let (linear, nonlinear) = partition isLinear ctxt

  -- Spits linear assumptions into splittable/not-splittable. Where splittable
  -- means that it is a data constructor at the highest level.
  let (splittable', unsplittable') =
        partition (isJust . snd) $ map (second getAssumConstr) linear
  let splittable = map (second fromJust) splittable'
  let unsplittable = map fst unsplittable'

  -- Get the relevant constructors for the splittable variables, and then
  -- actually generate the patterns.
  let relConstructors = relevantDataConstrs constructors splittable
  linearPatterns <-
    mapM (uncurry (buildConstructorPatterns span)) relConstructors

  -- Convert the unsplittables into plain variable patterns.
  let variablePatterns = map (buildVariablePatterns span) unsplittable

  -- Convert the discharged types into boxed patterns.
  let boxPatterns = map (buildBoxPattern span . fst) nonlinear

  let allPatterns = linearPatterns <> boxPatterns <> variablePatterns

  -- Order patterns into the same ordering as the context.
  let orderedPatterns =
        map (\(id, _) -> (id, fromJust $ lookup id allPatterns)) ctxt

  -- Convert the patterns into cases (i.e. Cartesian product of patterns).
  let cases = combineCases orderedPatterns

  -- The Nothing case should be unreachable, as this function is only ever
  -- called after checkEquation where equationTy is set.
  st <- get
  case equationTy st of
    Nothing -> return ([], [])
    Just eqTy -> do
      -- Filter the patterns if they are impossible.
      patternsAndMaybeBinders <- mapM (caseFilter span eqTy) (snd cases)
      validPatterns <- return $ catMaybes patternsAndMaybeBinders
      return (fst cases, validPatterns)

-- Wrapper around validateCase which updates the state when the case is valid.
caseFilter :: (?globals :: Globals)
  => Span
  -> Type
  -> [Pattern ()]
  -> Checker (Maybe ([Pattern ()], Ctxt Assumption))
caseFilter span ty pats = do
  (result, local) <- peekChecker $ validateCase span ty pats
  case result of
    Right (Just binders) -> local >> return (Just (pats, binders))
    _ -> return Nothing

-- Checks a case (i.e. list of patterns) against a type for validity.
-- If it is valid, return Just of the binding envionrment geneated
validateCase :: (?globals :: Globals)
  => Span
  -> Type
  -> [Pattern ()]
  -> Checker (Maybe (Ctxt Assumption))
validateCase span ty pats = do
  st <- get
  newConjunct

  -- Get local vars for the patterns and generate the relevant predicate
  -- (stored in the stack).
  (binders, _, localVars, _, _, _) <-
    ctxtFromTypedPatterns span ty pats (map (const NotFull) pats)
  pred <- popFromPredicateStack

  -- Build the type variable environment for proving the predicate
  tyVars <- tyVarContextExistential >>= justCoeffectTypesConverted span

  -- Quantify the predicate by the existence of all local variables.
  let thm = foldr (uncurry Exists) pred localVars
  result <- liftIO $ provePredicate thm tyVars

  case result of
    QED -> return (Just binders)
    _   -> return Nothing

  where
    popFromPredicateStack = do
      st <- get
      return . head . predicateStack $ st

-- Returns a context linking variables to a context linking their types to
-- their data constructors. The list of potential IDs is drawn from name
-- annotations on types in data definitions.
relevantDataConstrs ::
     Ctxt (Ctxt (TypeScheme, Substitution))
  -> Ctxt Id
  -> Ctxt (Ctxt [Maybe Id])
relevantDataConstrs constructors types =
  let
    -- Given a data type name, generates a context mappings its constructors
    -- names to a list of potential identifiers for its parameters. The length
    -- of this list is the arity of the constructor.
    getConstructorInfo :: Id -> Maybe (Ctxt [Maybe Id])
    getConstructorInfo dataId = do
        dataIdsConstrs <- lookup dataId constructors
        let consNames = map fst dataIdsConstrs
        let consTyNames = map (tsTypeNames . fst . snd) dataIdsConstrs
        return (zip consNames consTyNames)
    -- A list of all identifiers in context, e.g. x, xs.
    varIdentifiers :: [Id]
    varIdentifiers = map fst types
    -- Data constructors and their arities (as lists of Maybe Id).
    constructorInfo :: [Ctxt [Maybe Id]]
    constructorInfo = mapMaybe (getConstructorInfo . snd) types
  in zip varIdentifiers constructorInfo

-- Gets a potential constructor identifier on a type constructor, recursively.
getAssumConstr :: Assumption -> Maybe Id
getAssumConstr (Discharged _ _) = Nothing
getAssumConstr (Linear t) = getTypeConstr t
  where
    getTypeConstr :: Type -> Maybe Id
    getTypeConstr (FunTy _ t1 _) = Nothing
    getTypeConstr (TyCon id) = Just id
    getTypeConstr (Box _ t) = getTypeConstr t
    getTypeConstr (Diamond t1 _) = getTypeConstr t1
    getTypeConstr (TyApp t1 t2) = getTypeConstr t1
    getTypeConstr (TyVar _) = Nothing
    getTypeConstr (TyInt _) = Nothing
    getTypeConstr (TyInfix _ _ _) = Nothing
    getTypeConstr (TySet _) = Nothing
    getTypeConstr (TySig t _) = getTypeConstr t

-- Given a list of data constructors, generates patterns corresponding to them.
buildConstructorPatterns ::
     Span
  -> Id
  -> Ctxt [Maybe Id]
  -> Checker (Id, [Pattern ()])
buildConstructorPatterns span id constructors = do
  patterns <- mapM mkPat constructors
  return (id, patterns)
  where
    -- Generates a pattern for a data constructor, given its name and a list of
    -- (potential) argument names.
    mkPat :: (Id, [Maybe Id]) -> Checker (Pattern ())
    mkPat (name, ids) = do
      vars <- genFresh ids
      return $ PConstr span () False name (map (PVar span () False) vars)

    -- Generates a list of fresh identifiers, using the potential ids where
    -- possible, and defaulting to a freshening of the id paramter to
    -- `buildConstructorPatterns`.
    genFresh :: [Maybe Id] -> Checker [Id]
    genFresh ids = do
      let baseIds = map (fromMaybe id) ids
      freshStrings <- mapM (freshIdentifierBase . (\(Id x _) -> x)) baseIds
      return $ map mkId freshStrings

-- Given an identifier, builds the base pattern for that identifier, paired
-- with the identifier itself.
buildVariablePatterns :: Span -> Id -> (Id, [Pattern ()])
buildVariablePatterns span id = (id, pure $ PVar span () False id)

-- Given an identifier, generates a box pattern containing that identifier,
-- paired with the identifier itself.
buildBoxPattern :: Span -> Id -> (Id, [Pattern ()])
buildBoxPattern span id = (id, pure $ PBox span () False (PVar span () False id))

-- Accumulates identifiers which label function types.
tsTypeNames :: TypeScheme -> [Maybe Id]
tsTypeNames (Forall _ _ _ t) = typeNames t
   where
     typeNames :: Type -> [Maybe Id]
     typeNames (FunTy id _ t2) = id : typeNames t2
     typeNames _ = []

-- Given a context of patterns, couples the IDs with the Cartesian product of
-- the patterns.
combineCases :: Ctxt [Pattern ()] -> ([Id], [[Pattern ()]])
combineCases pats = (map fst pats, mapM snd pats)
