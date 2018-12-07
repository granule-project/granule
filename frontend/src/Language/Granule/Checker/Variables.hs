{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.Variables where

import Control.Monad.Trans.Maybe
import Control.Monad.State.Strict

import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Context
import Language.Granule.Utils

-- | Generate a fresh alphanumeric variable name
freshVar :: String -> MaybeT Checker String
freshVar s = do
  checkerState <- get
  let v = uniqueVarIdCounter checkerState
  put checkerState { uniqueVarIdCounter = v + 1 }
  return $ s <> "." <> show v

-- | Helper for creating a few (existential) coeffect variable of a particular
--   coeffect type.
freshCoeffectVar :: (?globals :: Globals) => Id -> Type -> MaybeT Checker Id
freshCoeffectVar cvar ty =
    freshCoeffectVarWithBinding cvar ty InstanceQ

-- | Helper for creating a few (existential) coeffect variable of a particular
--   coeffect type.
freshCoeffectVarWithBinding ::
   (?globals :: Globals) => Id -> Type -> Quantifier -> MaybeT Checker Id
freshCoeffectVarWithBinding cvar ty q = do
    freshName <- freshVar (internalName cvar)
    let cvar' = mkId freshName
    registerCoeffectVar cvar' ty q
    return cvar'

-- | Helper for registering a new coeffect variable in the checker
registerCoeffectVar ::
   (?globals :: Globals) => Id -> Type -> Quantifier -> MaybeT Checker ()
registerCoeffectVar v t q = do
  -- Check that the type is actual of kind Coeffect
  k <- inferKindOfType nullSpan t
  if k == KCoeffect then
    modify (\st -> st { tyVarContext = (v, (promoteTypeToKind t, q)) : tyVarContext st })
  else
    error $ "Granule bug: trying to register the following type as a coeffect " ++ pretty t

-- Erase a variable from the context
eraseVar :: Ctxt Assumption -> Id -> Ctxt Assumption
eraseVar [] _ = []
eraseVar ((var, t):ctxt) var' | var == var' = ctxt
                             | otherwise = (var, t) : eraseVar ctxt var'
