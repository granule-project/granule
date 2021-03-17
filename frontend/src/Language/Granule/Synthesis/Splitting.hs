{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Language.Granule.Synthesis.Splitting (generateCases) where

import Control.Arrow (second)
import Control.Monad.State.Strict (get, liftIO)
import Data.List (partition)
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust, mapMaybe)

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
-- the form of a pair of identifiers and lists of lists of patterns which
-- correspond to those identifiers. This generates cases for *all* variables in
-- the context, but only splits those in the toSplit list.
generateCases :: (?globals :: Globals)
  => Span
  -> Ctxt (Ctxt (TypeScheme, Substitution))
  -> Ctxt Assumption
  -> [Id]
  -> Checker ([Id], [([Pattern ()], Ctxt Assumption)])
generateCases span constructors ctxt toSplit = do
  -- Creates two subcontexts based on whether a variable should be split or not.
  let splitCtxt = relevantSubCtxt toSplit ctxt
  let noSplitCtxt = deleteVars ctxt toSplit

  -- Split the variables we want to.
  splitPatterns <- splitAll span constructors splitCtxt
  -- Convert the variables we don't wish to split to trivial patterns.
  let noSplitPatterns =
        map (buildVariablePatterns span) (getCtxtIds noSplitCtxt)

  let allPatterns = splitPatterns <> noSplitPatterns

  -- Arrange patterns into the same ordering as the context.
  let orderedPatterns =
        map (\(id, _) -> (id, fromJust $ lookup id allPatterns)) ctxt

  -- Convert the patterns into cases (i.e. Cartesian product across patterns).
  let cases = combineCases orderedPatterns

  -- The Nothing case should be unreachable, as this function is only ever
  -- called after checkEquation, where equationTy is set.
  st <- get
  case equationTy st of
    Nothing -> return ([], [])
    Just eqTy -> do
      -- Filter the patterns if they are impossible.
      patternsAndMaybeBinders <- mapM (caseFilter span eqTy) (snd cases)
      let validPatterns = catMaybes patternsAndMaybeBinders
      return (fst cases, validPatterns)

-- Splits all variables in a given context into a list of patterns.
splitAll ::
     Span
  -> Ctxt (Ctxt (TypeScheme, Substitution))
  -> Ctxt Assumption
  -> Checker (Ctxt [Pattern ()])
splitAll span constructors ctxt = do
  -- Partition the variables we will split by whether they are boxed or not.
  let (boxed, notBoxed) = partition (isBoxed . snd) ctxt

  -- Splits those variables not in boxes, where possible.
  (linearPatterns, unsplittable) <- splitNotBoxed span constructors notBoxed

  -- Convert the unsplittables into plain variable patterns.
  let variablePatterns =
        map (buildVariablePatterns span) unsplittable

  -- Convert the boxed types into boxed patterns, which may be split recursively
  -- until we reach a non-box.
  boxPatterns <- splitBoxed span constructors boxed

  let allPatterns = linearPatterns <> boxPatterns <> variablePatterns
  return allPatterns

-- Performs case splits on a series of variables which are *not* boxes. Returns
-- a tuple of patterns and unsplittable variable IDs.
splitNotBoxed ::
     Span
  -> Ctxt (Ctxt (TypeScheme, Substitution))
  -> Ctxt Assumption
  -> Checker (Ctxt [Pattern ()], [Id])
splitNotBoxed _ _ [] = pure ([], [])
splitNotBoxed span constructors ctxt = do
  -- Spits linear assumptions into splittable/not-splittable. Where splittable
  -- means that it is a data constructor at the highest level (note we filtered
  -- out box patterns in the previous step).
  let (splittable', unsplittable') =
        partition (isJust . snd) $ map (second getAssumConstr) ctxt
  let splittable = map (second fromJust) splittable'
  let unsplittable = getCtxtIds unsplittable'

  -- Get the relevant constructors for the splittable variables, and then
  -- actually generate the patterns.
  let relConstructors = relevantDataConstrs constructors splittable
  linearPatterns <-
    mapM (uncurry (buildConstructorPatterns span)) relConstructors

  return (linearPatterns, unsplittable)

-- Performs case splits on a series of variables which *are* boxes. Returns a
-- context linking each variable to its corresponding to patterns. Note that
-- we recursively split boxes until we reach something that isn't a box, then
-- split that once.
splitBoxed ::
     Span
  -> Ctxt (Ctxt (TypeScheme, Substitution))
  -> Ctxt Assumption
  -> Checker (Ctxt [Pattern ()])
splitBoxed _ _ [] = pure []
splitBoxed span constructors ctxt = do
  -- Gets the type inside the box.
  let extractSubtype t =
        case t of
          Linear (Box _ t') -> Linear t'
          Discharged (Box _ t') cf -> Discharged t' cf
          t -> t -- Note: this case should never be reached.
  let subtypeCtxt = map (second extractSubtype) ctxt

  -- Recursively split all variables, using their subtype.
  allPatterns <- splitAll span constructors subtypeCtxt

  -- We box all of the patterns generated to get the result.
  let result = map (second (map (buildBoxPattern span))) allPatterns
  return result

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
    ctxtFromTypedPatterns span (expandGrades ty) pats (map (const NotFull) pats)
  pred <- popFromPredicateStack

  -- Build the type variable environment for proving the predicate
  tyVars <- tyVarContextExistential >>= justCoeffectTypes span

  -- Quantify the predicate by the existence of all local variables.
  let thm = foldr (uncurry Exists) pred localVars
  constructors <- allDataConstructorNames
  (_, result) <- liftIO $ provePredicate thm tyVars constructors

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
getAssumConstr a =
  case a of
    (Discharged t _) -> getTypeConstr t
    (Linear t) -> getTypeConstr t
    (Ghost t _) -> getTypeConstr t
  where
    getTypeConstr :: Type -> Maybe Id
    getTypeConstr (Type _) = Nothing
    getTypeConstr (FunTy _ t1 _) = Nothing
    getTypeConstr (TyCon id) = Just id
    getTypeConstr (Box _ t) = getTypeConstr t
    getTypeConstr (Diamond t1 _) = getTypeConstr t1
    getTypeConstr (TyApp t1 t2) = getTypeConstr t1
    getTypeConstr (TySig t _) = getTypeConstr t
    getTypeConstr (TyVar _) = Nothing
    getTypeConstr (TyInt _) = Nothing
    getTypeConstr (TyRational _) = Nothing
    getTypeConstr (TyGrade _ _) = Nothing
    getTypeConstr (TyInfix _ _ _) = Nothing
    getTypeConstr (TySet _ _) = Nothing
    getTypeConstr (TyCase _ cases) =
      if allSame (map snd cases)
        then getTypeConstr . snd . head $ cases
        else Nothing
     where
       allSame [] = True
       allSame [x] = True
       allSame (x:(y:xs)) =
         if x == y then allSame xs else False

-- Given a function type, expand grades on parameters to be more permissive,
-- for the purpose of generating theorems. Exact natural number grades greater
-- than 1 are converted to intervals from 1 to that natural number. Interval
-- grades on the natural numbers with a lower bound greater than 1 are given 1
-- as a new lower bound. This is because when case splitting, we generate a
-- single usage from the pattern match.
expandGrades :: Type -> Type
expandGrades (FunTy id t1 t2) = FunTy id (expandGrades t1) (expandGrades t2)
expandGrades (Box (TyInfix TyOpInterval (TyGrade k lower) (TyGrade k' upper)) t) | lower > 1 =
  Box (TyInfix TyOpInterval (TyGrade k 1) (TyGrade k' upper)) t
expandGrades (Box (TyInfix TyOpInterval (TyInt lower) (TyInt upper)) t) | lower > 1 =
  Box (TyInfix TyOpInterval (TyInt 1) (TyInt upper)) t
expandGrades (Box (TyGrade k n) t) | n > 1 = Box (TyInfix TyOpInterval (TyGrade k 1) (TyGrade k n)) t
expandGrades (Box (TyInt n) t) | n > 1 = Box (TyInfix TyOpInterval (TyInt 1) (TyInt n)) t
expandGrades ty = ty

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

-- Wraps a pattern in a box
buildBoxPattern :: Span -> Pattern () -> Pattern ()
buildBoxPattern span = PBox span () False

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

-- Determines whether an assumption contains a box type.
isBoxed :: Assumption -> Bool
isBoxed (Linear (Box _ _)) = True
isBoxed (Discharged (Box _ _) _) = True
isBoxed _ = False
