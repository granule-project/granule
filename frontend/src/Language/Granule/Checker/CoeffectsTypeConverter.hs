module Language.Granule.Checker.CoeffectsTypeConverter(justCoeffectTypesConverted, tyVarContextExistential) where

import Control.Monad.Except (catchError)
import Control.Monad.State.Strict
import Data.Maybe(catMaybes, mapMaybe)

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Substitution (checkKind)

import Language.Granule.Context

import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Utils

justCoeffectTypesConverted :: (?globals::Globals)
  => Span -> [(a, (Kind, b))] -> Checker [(a, (Type, b))]
justCoeffectTypesConverted s xs = catMaybes <$> mapM convert xs
  where
    convert (var, (KPromote t, q)) = (do
      st <- get
      k <- checkKind s (tyVarContext st) t KCoeffect
      return $ Just (var, (t, q))) `catchError` const (return Nothing)
    convert (var, (KVar v, q)) = (do
      st <- get
      k <- checkKind s (tyVarContext st) (TyVar v) KCoeffect
      return $ Just (var, (TyVar v, q))) `catchError` const (return Nothing)
    convert _ = return Nothing

-- Convert all universal variables to existential
tyVarContextExistential :: Checker (Ctxt (Kind, Quantifier))
tyVarContextExistential = do
  st <- get
  return $ mapMaybe (\(v, (k, q)) ->
    case q of
      -- This makes splitting work when the LHS is a pattern, but not sure if it
      -- has adverse effects...
      -- BoundQ -> Nothing
      _      -> Just (v, (k, InstanceQ))) (tyVarContext st)