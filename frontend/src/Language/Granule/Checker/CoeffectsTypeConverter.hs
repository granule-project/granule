{-# LANGUAGE GADTs #-}
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

justCoeffectTypesConverted :: (?globals::Globals, Show a)
  => Span -> [(a, (TypeWithLevel, b))] -> Checker [(a, (Type One, b))]
justCoeffectTypesConverted s xs = mapM convert xs >>= (return . catMaybes)
  where
    convert (var, (TypeWithLevel (LSucc LZero) t, q)) = do
      debugM "convert" ("var = " ++ show var ++ ", t = " ++ show t)
      k <- inferKindOfType s t
      debugM "convert" ("k = " ++ show k)
      if isCoeffectKind k
        then return $ Just (var, (t, q))
        else return Nothing
    convert _ = return Nothing
-- justCoeffectTypesConvertedVars :: (?globals::Globals)
--   => Span -> [(Id, Kind)] -> Checker (Ctxt (Type One))
-- justCoeffectTypesConvertedVars s env = do
--   let implicitUniversalMadeExplicit = map (\(var, k) -> (var, (k, ForallQ))) env
--   env' <- justCoeffectTypesConverted s implicitUniversalMadeExplicit
--   return $ stripQuantifiers env'
-- Convert all universal variables to existential

tyVarContextExistential :: Checker (Ctxt (TypeWithLevel, Quantifier))
tyVarContextExistential = do
  st <- get
  return $ mapMaybe (\(v, (k, q)) ->
    case q of
      -- This makes splitting work when the LHS is a pattern, but not sure if it
      -- has adverse effects...
      -- BoundQ -> Nothing
      _      -> Just (v, (k, InstanceQ))) (tyVarContext st)