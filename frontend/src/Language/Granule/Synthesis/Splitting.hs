module Language.Granule.Synthesis.Splitting where

import Control.Arrow (second)
import Control.Monad (replicateM)
import Data.Maybe (mapMaybe)
import Data.List (partition)

import Language.Granule.Checker.Monad
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Variables

import Language.Granule.Context

import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pattern

generateCases ::
    Span
    -> Ctxt (Ctxt (TypeScheme, Substitution))
    -> Ctxt Assumption
    -> Checker (Ctxt [Pattern ()])
generateCases span constructors ctxt = do
  let isLinear (_, a) = case a of Linear _ -> True ; Discharged _ _ -> False
  let (linear, discharged) = partition isLinear ctxt

  let linearTypes = map (second getAssumConstr) linear
  let relConstructors = relevantDataConstrs constructors linearTypes
  linearPatterns <- mapM (uncurry (buildPatterns span)) relConstructors

  let boxPatterns = map (buildBoxPattern span . fst) discharged

  return $ linearPatterns ++ boxPatterns

-- Returns a context linking variables to a context linking their types to their data constructors.
relevantDataConstrs :: Ctxt (Ctxt (TypeScheme, Substitution)) -> Ctxt Id -> Ctxt (Ctxt (Id, Integer))
relevantDataConstrs constructors types =
  let typeSchemes = map fst
      constructorArities dataId = map ((,) dataId . tsArity . fst . snd)
      constructorInfo dataId = do
        dataIdsConstrs <- lookup dataId constructors
        return (typeSchemes dataIdsConstrs, constructorArities dataId dataIdsConstrs)
  in  zip (map fst types) (map (uncurry zip) (mapMaybe (constructorInfo . snd) types))

getAssumConstr :: Assumption -> Id
getAssumConstr (Linear t) = getTypeConstr t
getAssumConstr (Discharged t _) = undefined -- Unreachable

getTypeConstr :: Type -> Id
getTypeConstr (FunTy t1 _) = undefined
getTypeConstr (TyCon id) = id
getTypeConstr (Box _ t) = getTypeConstr t
getTypeConstr (Diamond t1 _) = getTypeConstr t1
getTypeConstr (TyApp t1 t2) = getTypeConstr t1
getTypeConstr (TyVar id) = id
getTypeConstr (TyInt _) = undefined
getTypeConstr (TyInfix _ _ _) = undefined
getTypeConstr (TySet _) = undefined

buildPatterns :: Span -> Id -> Ctxt (Id, Integer) -> Checker (Id, [Pattern ()])
buildPatterns span id constructors = do
  patterns <- mapM mkPat constructors
  return (id, patterns)
  where
    mkPat :: (Id, (Id, Integer)) -> Checker (Pattern ())
    mkPat (name, (_, nVars)) = do
      vars <- nFresh nVars
      return $ PConstr span () name (map (PVar span ()) vars)
    nFresh :: Integer -> Checker [Id]
    nFresh n = do
      freshStrings <- replicateM (fromInteger n) (freshIdentifierBase ((\ (Id x _) -> x) id))
      return $ map mkId freshStrings

buildBoxPattern :: Span -> Id -> (Id, [Pattern ()])
buildBoxPattern span id = (id, pure $ PBox span () (PVar span () id))

tsArity :: TypeScheme -> Integer
tsArity (Forall _ _ _ t) = tArity t

tArity :: Type -> Integer
tArity (FunTy t1 t2) = 1 + tArity t2
tArity _ = 0

combineCases :: Ctxt [Pattern ()] -> ([Id], [[Pattern ()]])
combineCases pats = (map fst pats, mapM snd pats)