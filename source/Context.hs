-- Provide general contexts used in the both the
-- checker and the interpreter

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Context where

import Data.Maybe (isJust)
import Data.List (sortBy)
import Syntax.Expr (Id)

-- | Type of contexts
type Ctxt t = [(Id, t)]

-- | Extend an context with a new value
extend :: Ctxt a -> Id -> a -> Ctxt a
extend ctxt x v = (x, v) : ctxt

-- | Empty context
empty :: Ctxt a
empty = []

-- | Replace the first occurence of an item in an context
replace :: Ctxt a -> Id -> a -> Ctxt a
replace [] name v
  = [(name, v)]
replace ((name', _):ctxt) name v | name == name'
  = (name', v) : ctxt
replace (x : ctxt) name v
  = x : replace ctxt name v

-- $setup
-- >>> import Syntax.Expr (mkId)
{- | Take the intersection of two contexts based on keys
NOTE: this is not a commutative action, consider:
>>> intersectCtxts [(mkId "x",1)] [(mkId "x",2)]
[(Id "x" "x",1)]
-}
intersectCtxts :: Ctxt a -> Ctxt a -> Ctxt a
intersectCtxts a b = normaliseCtxt $ filter (appearsIn b) a
  where appearsIn x (name, _) = isJust $ lookup name x

{- | `subtractCtxt a b` removes all the key-value pairs from
   `a` that have keys in `b` -}
subtractCtxt :: Ctxt a -> Ctxt a -> Ctxt a
subtractCtxt a b = filter (not . appearsIn b) a
  where appearsIn x (name, _) = isJust $ lookup name x

-- | Normalise an context by sorting based on the keys
normaliseCtxt :: Ctxt a -> Ctxt a
normaliseCtxt = sortBy (\x y -> fst x `compare` fst y)

-- Delete an entry from an context
deleteVar :: Id -> Ctxt t -> Ctxt t
deleteVar _ [] = []
deleteVar x ((y, b) : m) | x == y = deleteVar x m
                         | otherwise = (y, b) : deleteVar x m
