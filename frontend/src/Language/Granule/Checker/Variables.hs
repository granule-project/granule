{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Granule.Checker.Variables where

import Control.Monad.State.Strict

import qualified Data.Map as M

import Language.Granule.Context
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.FirstParameter

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
freshTyVarInContext :: HasLevel l => Id -> Type l -> Checker Id
freshTyVarInContext cvar k = do
    freshTyVarInContextWithBinding cvar k InstanceQ

-- | Helper for creating a few (existential) coeffect variable of a particular
--   coeffect type.
freshTyVarInContextWithBinding :: HasLevel l => Id -> Type l -> Quantifier -> Checker Id
freshTyVarInContextWithBinding var k q = do
    freshName <- freshIdentifierBase (internalName var)
    let var' = mkId freshName
    registerTyVarInContext var' k q
    return var'

-- | Helper for registering a new coeffect variable in the checker
registerTyVarInContext :: HasLevel l => Id -> Type l -> Quantifier -> Checker ()
registerTyVarInContext v t q = do
    modify (\st -> st { tyVarContext = (v, (TypeWithLevel (getLevel t) t, q)) : tyVarContext st })

lookupAtLevel :: (FirstParameter f TypeWithLevel)
              => Span
              -> Id
              -> Ctxt f
              -> ULevel l
              -> Checker (Maybe (Type l))
lookupAtLevel s v ctxt level =
  case lookup v ctxt of
    Just (getFirstParameter -> tl@(TypeWithLevel level' t)) ->
      -- Does the level match what we want?
      case isAtLevel level' t level of
        Just t' -> return $ Just t'
        Nothing -> throw $ WrongLevel s tl (IsLevel level)
    Nothing -> return Nothing