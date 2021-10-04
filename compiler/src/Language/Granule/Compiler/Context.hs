-- |

{-# LANGUAGE NamedFieldPuns #-}
module Language.Granule.Compiler.Context where

--import Control.Monad.State
--import Data.Functor
import Data.Map (Map)
import qualified Data.Map as Map
--import Language.Granule.Compiler.Gensym
--import Language.Granule.Compiler.Util

-- |
data Ctxt a b = Ctxt {
                  -- |
                  dest :: a,
                  -- |
                  env :: Map a b  }
  deriving Show

newCtxt :: a -> b -> Ctxt a b
newCtxt k v = Ctxt { dest = k, env = Map.singleton k v }

extendCtxt :: Ord a => Ctxt a b -> a -> b -> Ctxt a b
extendCtxt ctx@Ctxt{env} k v = ctx { env = Map.insert k v env }

lookupCtxt :: Ord a => Ctxt a b -> a -> Maybe b
lookupCtxt ctx@Ctxt{env} k = Map.lookup k env
