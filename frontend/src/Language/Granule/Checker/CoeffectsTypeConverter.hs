module Language.Granule.Checker.CoeffectsTypeConverter(justCoeffectTypesConverted, tyVarContextExistential) where

import Control.Monad.State.Strict
import Data.Maybe(catMaybes, mapMaybe)

import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates

import Language.Granule.Context

import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Utils

justCoeffectTypesConverted :: (?globals::Globals)
  => Span -> [(a, (Kind, b))] -> Checker [(a, (Type, b))]
justCoeffectTypesConverted s xs = catMaybes <$> mapM convert xs
  where
    convert (var, (KPromote t, q)) = do
      k <- inferKindOfType s t
      if isCoeffectKind k
        then return $ Just (var, (t, q))
        else return Nothing
    convert (var, (KVar v, q)) = do
      k <- inferKindOfType s (TyVar v)
      if isCoeffectKind k
        then return $ Just (var, (TyVar v, q))
        else return Nothing
    convert _ = return Nothing

-- Convert all universal variables to existential
tyVarContextExistential :: Checker (Ctxt (Kind, Quantifier))
tyVarContextExistential = do
  st <- get
  return $ mapMaybe (\(v, (k, q)) ->
    case q of
      BoundQ -> Nothing
      _      -> Just (v, (k, InstanceQ))) (tyVarContext st)