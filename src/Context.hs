{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Context where

import Syntax.Expr
import Syntax.Pretty
import Data.List
import Data.Maybe
import Data.Either
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Control.Monad
import Data.SBV
import qualified Data.Set as S

-- Environments
type Env t = [(Id, t)]

-- Extend a context with a new value
extend :: Env a -> Id -> a -> Env a
extend env x v = (x, v) : env

-- Empty environment
empty :: Env a
empty = []

-- Replace the first occurence of an item in an environment
replace :: Env a -> Id -> a -> Env a
replace [] id v
  = [(id, v)]
replace ((id', _):env) id v | id == id'
  = (id', v) : env
replace (x : env) id v
  = x : replace env id v

-- Take the intersection of two environments
keyIntersect :: Env a -> Env a -> Env a
keyIntersect a b = sortBy (\a b -> fst a `compare` fst b) $ filter (appearsIn a) b
  where appearsIn a (id, _) = isJust $ lookup id a


-- Delete an entry from an environment
deleteVar :: Id -> Env t -> Env t
deleteVar _ [] = []
deleteVar x ((y, b) : m) | x == y = deleteVar x m
                         | otherwise = (y, b) : deleteVar x m

unrename :: [(Id, Id)] -> Id -> Id
unrename nameMap var =
    case lookup var (map swap nameMap) of
      Just var' -> var'
      Nothing  -> var
  where swap (a, b) = (b, a)