{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.Variables where

import Control.Monad.State.Strict

import qualified Data.Map as M

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

-- | Helper for creating a new (existential) coeffect variable of a particular
--   coeffect type.
freshTyVarInContext :: Id -> Kind -> TyVarOrigin -> Checker Id
freshTyVarInContext cvar k = do
    freshTyVarInContextWithBinding cvar k InstanceQ

-- | Helper for creating a new (existential) coeffect variable of a particular
--   coeffect type.
freshTyVarInContextWithBinding :: Id -> Kind -> Quantifier -> TyVarOrigin -> Checker Id
freshTyVarInContextWithBinding var k q o = do
    freshName <- freshIdentifierBase (internalName var)
    let var' = mkId freshName
    registerTyVarInContext var' k q o
    return var'

-- | Helper for registering a new coeffect variable in the checker
registerTyVarInContext :: Id -> Kind -> Quantifier -> TyVarOrigin -> Checker ()
registerTyVarInContext v k q o = do
  modify (\st -> st { tyVarContext = (v, (k, q, o)) : tyVarContext st })

-- Erase a variable from the context
eraseVar :: Ctxt Assumption -> Id -> Ctxt Assumption
eraseVar [] _ = []
eraseVar ((var, t):ctxt) var' | var == var' = ctxt
                              | otherwise = (var, t) : eraseVar ctxt var'
