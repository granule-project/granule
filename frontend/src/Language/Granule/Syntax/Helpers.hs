{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Granule.Syntax.Helpers where

import Data.List (delete)
import Control.Monad.Trans.State.Strict
import Control.Monad.Identity

import Language.Granule.Syntax.Identifiers

class Freshenable m t where
  -- Alpha-convert bound variables to avoid name capturing
  freshen :: Monad m => t -> Freshener m t

class Term t where
  -- Compute the free variables in an open term
  freeVars :: t -> [Id]

-- Used to distinguish the value-level and type-level variables
data IdSyntacticCategory = Value | Type

-- | The freshening monad for alpha-conversion to avoid name capturing
type Freshener m t = StateT FreshenerState m t

data FreshenerState = FreshenerState
  { counter :: Int -- ^ fresh Id counter
  , varMap :: [(String, String)] -- ^ mapping of variables to their fresh names
  , tyMap  :: [(String, String)] -- ^ mapping of type variables to fresh names
  } deriving Show

-- | Given something freshenable,
-- | e.g. the AST, run the freshener on it and return the final state
runFreshener :: Freshenable Identity t => t -> t
runFreshener x = runIdentity $ runFreshenerM (freshen x)

runFreshenerM :: Monad m => Freshener m t -> m t
runFreshenerM x =
  evalStateT x FreshenerState { counter = 0, varMap = [], tyMap = [] }

removeFreshenings :: Monad m => [Id] -> Freshener m ()
removeFreshenings [] = return ()
removeFreshenings (x:xs) = do
    st <- get
    put st { varMap = delete x' (varMap st) }
    removeFreshenings xs
  where
    x' = (sourceName x, internalName x)

-- Helper in the Freshener monad, creates a fresh id (and
-- remembers the mapping).
freshIdentifierBase :: Monad m => IdSyntacticCategory -> Id -> Freshener m Id
freshIdentifierBase cat var = do
    st <- get
    let var' = sourceName var <> "_" <> show (counter st)
    case cat of
      Value -> put st { counter = (counter st) + 1, varMap = (sourceName var, var') : (varMap st) }
      Type  -> put st { counter = (counter st) + 1,  tyMap = (sourceName var, var') :  (tyMap st) }
    return var { internalName = var' }

-- | Look up a variable in the freshener state.
-- If @Nothing@ then the variable name shouldn't change
lookupVar :: Monad m => IdSyntacticCategory -> Id -> Freshener m (Maybe String)
lookupVar cat v = do
  st <- get
  case cat of
    Value -> return . lookup (sourceName v) . varMap $ st
    Type  -> return . lookup (sourceName v) .  tyMap $ st
