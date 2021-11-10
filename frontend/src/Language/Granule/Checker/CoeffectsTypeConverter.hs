{-# LANGUAGE GADTs #-}
module Language.Granule.Checker.CoeffectsTypeConverter(includeOnlyGradeVariables, tyVarContextExistential) where

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

-- Filters a type variable context to include only variables which
-- have a grade type
includeOnlyGradeVariables :: (?globals :: Globals)
  => Span -> Ctxt (Type, b) -> Checker (Ctxt (Type, b))
includeOnlyGradeVariables s xs = mapM convert xs >>= (return . catMaybes)
  where
    convert (var, (t, q)) = (do
      k <- checkKind s t kcoeffect <|> checkKind s t keffect
      return $ Just (var, (t, q))) `catchError` const (return Nothing)

tyVarContextExistential :: Checker (Ctxt (Type, Quantifier))
tyVarContextExistential = do
  st <- get
  return $ flip mapMaybe (tyVarContext st) $ \(v, (k, q)) ->
    case q of
      -- This makes splitting work when the LHS is a pattern, but not sure if it
      -- has adverse effects...
      -- BoundQ -> Nothing
      _ -> Just (v, (k, InstanceQ))
      -- _      -> Just (v, (k, q))