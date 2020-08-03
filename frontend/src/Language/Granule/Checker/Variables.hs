{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.Variables where

import Control.Monad.State.Strict

import qualified Data.Map as M

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type

-- | Generate a fresh alphanumeric identifier name string
freshIdentifierBase :: String -> Checker String
freshIdentifierBase s = do
  checkerState <- get
  let vmap = uniqueVarIdCounterMap checkerState
  let s' = takeWhile (\c -> c /= '`') s
  case M.lookup s' vmap of
    Nothing -> do
      let vmap' = M.insert s' 1 vmap
      put checkerState { uniqueVarIdCounterMap = vmap' }
      return $ s' <> "." <> show 0

    Just n -> do
      let vmap' = M.insert s' (n+1) vmap
      put checkerState { uniqueVarIdCounterMap = vmap' }
      return $ s' <> "." <> show n

-- | Helper for creating a few (existential) coeffect variable of a particular
--   coeffect type.
freshTyVarInContext :: Id -> Kind -> Checker Id
freshTyVarInContext cvar k = do
    freshTyVarInContextWithBinding cvar k InstanceQ

-- | Helper for creating a few (existential) coeffect variable of a particular
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
    -- Add to the predicate
    case q of
      ForallQ -> universal v k
      _       -> existential v k