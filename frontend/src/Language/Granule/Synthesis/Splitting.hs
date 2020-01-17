module Language.Granule.Synthesis.Splitting ( generateCases ) where

import Control.Arrow (second)
import Control.Monad (filterM, mapM)
import Control.Monad.State.Strict
import Data.List (partition)
import Data.Maybe (fromJust, fromMaybe, isJust, mapMaybe)

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

generateCases :: (?globals :: Globals)
  => Span
  -> Type
  -> Ctxt (Ctxt (TypeScheme, Substitution))
  -> Ctxt Assumption
  -> Checker ([Id], [[Pattern ()]])
generateCases span ty constructors ctxt = do
  let isLinear (_, a) =
        case a of
          Linear (Box _ _) -> False
          Linear _ -> True
          Discharged _ _ -> False
  let (linear, discharged) = partition isLinear ctxt
  let (splittable', unsplittable') =
        partition (isJust . snd) $ map (second getAssumConstr) linear
  let splittable = map (second fromJust) splittable'
  let unsplittable = map fst unsplittable'
  let relConstructors = relevantDataConstrs constructors splittable
  linearPatterns <-
    mapM (uncurry (buildConstructorPatterns span)) relConstructors
  let variablePatterns = map (buildVariablePatterns span) unsplittable
  let boxPatterns = map (buildBoxPattern span . fst) discharged
  let allPatterns = linearPatterns ++ boxPatterns ++ variablePatterns
  let orderedPatterns =
        map (\(id, _) -> (id, fromJust $ lookup id allPatterns)) ctxt
  let tys =
        map
          ((\a -> case a of Linear x -> x; Discharged x _ -> x) . snd)
          ctxt ++ [ty]
  let funTy = foldr1 (FunTy Nothing) tys
  let cases = combineCases orderedPatterns
  validPatterns <- filterM (caseFilter span funTy) (snd cases)
  return (fst cases, validPatterns)

caseFilter :: (?globals :: Globals) => Span -> Type -> [Pattern ()] -> Checker Bool
caseFilter span ty pats = do
  (result, local) <- peekChecker $ validateCase span ty pats
  case result of
    Right True -> local >> pure True
    Right _ -> pure False
    Left err -> pure False

validateCase :: (?globals :: Globals) => Span -> Type -> [Pattern ()] -> Checker Bool
validateCase span ty pats = do
  st <- get
  newConjunct
  (patternGam, tau, localVars, subst, elaboratedPats, consumptions) <-
    ctxtFromTypedPatterns span ty pats (patternConsumption st)
  pred <- popFromPredicateStack
  tyVars <- tyVarContextExistential >>= justCoeffectTypesConverted span
  let thm = foldr (uncurry Exists) pred localVars
  result <- liftIO $ provePredicate thm tyVars
  case result of
    QED -> return True
    _ -> return False
  where
    popFromPredicateStack = do
      st <- get
      return . head . predicateStack $ st

-- Returns a context linking variables to a context linking their types to their data constructors.
relevantDataConstrs ::
     Ctxt (Ctxt (TypeScheme, Substitution))
  -> Ctxt Id
  -> Ctxt (Ctxt [Maybe Id])
relevantDataConstrs constructors types =
  let
    constructorInfo :: Id -> Maybe (Ctxt [Maybe Id])
    constructorInfo dataId = do
        dataIdsConstrs <- lookup dataId constructors
        let consNames = map fst dataIdsConstrs
        let consTyNames = map (tsTypeNames . fst . snd) dataIdsConstrs
        return (zip consNames consTyNames)
  in zip
       (map fst types)
       (mapMaybe (constructorInfo . snd) types)

getAssumConstr :: Assumption -> Maybe Id
getAssumConstr (Linear t) = getTypeConstr t
getAssumConstr (Discharged _ _) = Nothing

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

buildConstructorPatterns :: Span -> Id -> Ctxt [Maybe Id] -> Checker (Id, [Pattern ()])
buildConstructorPatterns span id constructors = do
  patterns <- mapM mkPat constructors
  return (id, patterns)
  where
    mkPat :: (Id, [Maybe Id]) -> Checker (Pattern ())
    mkPat (name, ids) = do
      vars <- genFresh ids
      return $ PConstr span () False name (map (PVar span () False) vars)
    genFresh :: [Maybe Id] -> Checker [Id]
    genFresh ids = do
      let baseIds = map (fromMaybe id) ids
      freshStrings <- mapM (freshIdentifierBase . (\(Id x _) -> x)) baseIds
      return $ map mkId freshStrings

buildVariablePatterns :: Span -> Id -> (Id, [Pattern ()])
buildVariablePatterns span id = (id, pure $ PVar span () False id)

buildBoxPattern :: Span -> Id -> (Id, [Pattern ()])
buildBoxPattern span id = (id, pure $ PBox span () False (PVar span () False id))

tsTypeNames :: TypeScheme -> [Maybe Id]
tsTypeNames (Forall _ _ _ t) = typeNames t

typeNames :: Type -> [Maybe Id]
typeNames (FunTy id _ t2) = id : typeNames t2
typeNames _ = []

combineCases :: Ctxt [Pattern ()] -> ([Id], [[Pattern ()]])
combineCases pats = (map fst pats, mapM snd pats)
