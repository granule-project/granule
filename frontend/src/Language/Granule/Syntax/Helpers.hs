{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

{-# options_ghc -Wno-orphans #-}

module Language.Granule.Syntax.Helpers where

import Data.List (delete)
import Control.Monad.Trans.State.Strict
import Control.Monad.Fail
import Control.Monad.Identity

import Language.Granule.Syntax.Identifiers

class Freshenable m t where
  -- Alpha-convert bound variables to avoid name capturing
  freshen :: Monad m => t -> Freshener m t

instance (Freshenable m a, Freshenable m b) => Freshenable m (a, b) where
  freshen (x, y) = do
    x <- freshen x
    y <- freshen y
    return (x, y)

instance Freshenable m a => Freshenable m [a] where
  freshen = mapM freshen

instance Freshenable m a => Freshenable m (Maybe a) where
  freshen Nothing = return Nothing
  freshen (Just x) = freshen x >>= return . Just

class Term t where
  -- Compute the free variables in an open term
  freeVars :: t -> [Id]

  -- Contains a hole (goal) somewhere
  hasHole :: t -> Bool
  hasHole _ = False

  -- Is an atomic term (used in pretty printing)
  isLexicallyAtomic :: t -> Bool
  isLexicallyAtomic _ = False

-- Used to distinguish the value-level and type-level variables
data IdSyntacticCategory = ValueL | TypeL

-- | The freshening monad for alpha-conversion to avoid name capturing
type Freshener m t = StateT FreshenerState m t

--instance MonadFail m => MonadFail (StateT FreshenerState m) where
--  fail = Control.Monad.Fail.fail

data FreshenerState = FreshenerState
  { counter :: Word -- ^ fresh Id counter
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
    put st { varMap = delete x' (varMap st)
           , tyMap = delete x' (tyMap st) }
    removeFreshenings xs
  where
    x' = (sourceName x, internalName x)

-- Helper in the Freshener monad, creates a fresh id (and
-- remembers the mapping).
freshIdentifierBase :: Monad m => IdSyntacticCategory -> Id -> Freshener m Id
freshIdentifierBase cat var = do
    st <- get
    let var' = sourceName var <> "`" <> show (counter st)
    case cat of
      ValueL -> put st { counter = (counter st) + 1, varMap = (sourceName var, var') : (varMap st) }
      TypeL  -> put st { counter = (counter st) + 1,  tyMap = (sourceName var, var') :  (tyMap st) }
    return var { internalName = var' }

-- | Look up a variable in the freshener state.
-- If @Nothing@ then the variable name shouldn't change
lookupVar :: Monad m => IdSyntacticCategory -> Id -> Freshener m (Maybe String)
lookupVar cat v = do
  st <- get
  case cat of
    ValueL -> return . lookup (sourceName v) . varMap $ st
    TypeL  -> return . lookup (sourceName v) .  tyMap $ st

instance MonadFail Identity where
  fail = error
