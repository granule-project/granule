-- Provide general environments (contexts) used in the both the
-- checker and the interpreter

module Context where

import Data.Maybe  (isJust)
import Data.List   (sortBy)
import Syntax.Expr (Id)

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
replace [] name v
  = [(name, v)]
replace ((name', _):env) name v | name == name'
  = (name', v) : env
replace (x : env) name v
  = x : replace env name v

-- Take the intersection of two environments based on keys
-- NOTE: this is not a commutative action, consider.
-- keyIntersect [("x", 1)] [("x", 2)] = [("x", 1)]
keyIntersect :: Env a -> Env a -> Env a
keyIntersect a b = sortBy (\x y -> fst x `compare` fst y) $ filter (appearsIn a) b
  where appearsIn x (name, _) = isJust $ lookup name x

-- `keyDelete a b` removes all the key-value pairs from
-- `a` that have keys in `b`
keyDelete :: Env a -> Env a -> Env a
keyDelete a b = filter (not . appearsIn b) a
  where appearsIn x (name, _) = isJust $ lookup name x

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
