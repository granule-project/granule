{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.Variables where

import Control.Monad.State.Strict

import qualified Data.Map as M
import Data.Maybe (fromMaybe)

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type

import Language.Granule.Context

-- | Generate a fresh alphanumeric identifier name string
freshIdentifierBase :: String -> Checker String
freshIdentifierBase s = do
  checkerState <- get
  let vmap = uniqueVarIdCounterMap checkerState
      s' = takeWhile (\c -> c /= '`') s
      counter = fromMaybe 0 $ M.lookup s' vmap
      vmap' = M.insert s' (counter+1) vmap
  put checkerState { uniqueVarIdCounterMap = vmap' }
  pure $ s' <> "." <> show counter

-- | Helper for creating a new (existential) coeffect variable of a particular
--   coeffect type.
freshTyVarInContext :: Id -> Kind -> Checker Id
freshTyVarInContext cvar k = do
    freshTyVarInContextWithBinding cvar k InstanceQ

-- | Helper for creating a new (existential) coeffect variable of a particular
--   coeffect type.
freshTyVarInContextWithBinding :: Id -> Kind -> Quantifier -> Checker Id
freshTyVarInContextWithBinding var k q = do
    freshName <- freshIdentifierBase (internalName var)
    let var' = mkId freshName
    registerTyVarInContext var' k q
    return var'

-- | Helper for registering a new coeffect variable in the checker
registerTyVarInContext :: Id -> Kind -> Quantifier -> Checker ()
registerTyVarInContext v k q = do
  modify (\st -> st { tyVarContext = (v, (k, q)) : tyVarContext st })

-- Erase a variable from the context
eraseVar :: Ctxt Assumption -> Id -> Ctxt Assumption
eraseVar [] _ = []
eraseVar ((var, t):ctxt) var' | var == var' = ctxt
                              | otherwise = (var, t) : eraseVar ctxt var'
