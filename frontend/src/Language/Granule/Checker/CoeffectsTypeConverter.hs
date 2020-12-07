{-# LANGUAGE GADTs #-}
module Language.Granule.Checker.CoeffectsTypeConverter(justCoeffectTypes, tyVarContextExistential) where

import Control.Monad.Except (catchError)
import Control.Monad.State.Strict
import Data.Maybe(catMaybes, mapMaybe)

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Kinding (checkKind)

import Language.Granule.Context

import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Utils

justCoeffectTypes :: (?globals :: Globals)
  => Span -> [(a, (Type, b))] -> Checker [(a, (Type, b))]
justCoeffectTypes s xs = mapM convert xs >>= (return . catMaybes)
  where
    convert (var, (t, q)) = (do
      k <- checkKind s t kcoeffect
      return $ Just (var, (t, q))) `catchError` const (return Nothing)

tyVarContextExistential :: Checker (Ctxt (Type, Quantifier))
tyVarContextExistential = do
  st <- get
  return $ mapMaybe (\(v, (k, q)) ->
    case q of
      -- This makes splitting work when the LHS is a pattern, but not sure if it
      -- has adverse effects...
      -- BoundQ -> Nothing
      _      -> Just (v, (k, InstanceQ))) (tyVarContext st)