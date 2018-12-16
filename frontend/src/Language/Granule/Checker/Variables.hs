{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.Variables where

import Control.Monad.Trans.Maybe
import Control.Monad.State.Strict

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type

import Language.Granule.Context
import Language.Granule.Utils

-- | Generate a fresh alphanumeric identifier name string
freshIdentifierBase :: String -> MaybeT Checker String
freshIdentifierBase s = do
  checkerState <- get
  let v = uniqueVarIdCounter checkerState
  put checkerState { uniqueVarIdCounter = v + 1 }
  return $ s <> "." <> show v

-- | Helper for creating a few (existential) coeffect variable of a particular
--   coeffect type.
freshTyVarInContext :: (?globals :: Globals) => Id -> Kind -> MaybeT Checker Id
freshTyVarInContext cvar ty =
    freshTyVarInContextWithBinding cvar ty InstanceQ

-- | Helper for creating a few (existential) coeffect variable of a particular
--   coeffect type.
freshTyVarInContextWithBinding ::
   (?globals :: Globals) => Id -> Kind -> Quantifier -> MaybeT Checker Id
freshTyVarInContextWithBinding cvar ty q = do
    freshName <- freshIdentifierBase (internalName cvar)
    let cvar' = mkId freshName
    registerTyVarInContext cvar' ty q
    return cvar'

-- | Helper for registering a new coeffect variable in the checker
registerTyVarInContext ::
   (?globals :: Globals) => Id -> Kind -> Quantifier -> MaybeT Checker ()
registerTyVarInContext v k q = do
  modify (\st -> st { tyVarContext = (v, (k, q)) : tyVarContext st })

-- Erase a variable from the context
eraseVar :: Ctxt Assumption -> Id -> Ctxt Assumption
eraseVar [] _ = []
eraseVar ((var, t):ctxt) var' | var == var' = ctxt
                              | otherwise = (var, t) : eraseVar ctxt var'
