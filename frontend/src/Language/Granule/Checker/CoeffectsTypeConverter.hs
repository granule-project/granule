module Language.Granule.Checker.CoeffectsTypeConverter(justCoeffectTypesConverted) where

import Data.Maybe(catMaybes)

import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Monad

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
