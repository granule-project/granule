-- Provide general contexts used in the both the
-- checker and the interpreter

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Granule.Context where

import Data.Maybe (isJust)
import Data.List (sortBy)
import Language.Granule.Syntax.Identifiers (Id)

-- | Type of contexts
type Ctxt t = [(Id, t)]

-- | Extend a context with a new value (shadowing an existing binder)
extendShadow :: Ctxt a -> Id -> a -> Ctxt a
extendShadow ctxt i v = (i, v) : ctxt

-- | Extend an context with a new value, ensure that the name is not in the context
extend :: Ctxt a -> Id -> a -> Maybe (Ctxt a)
extend ctxt i v = case lookup i ctxt of
  Nothing -> Just ((i, v) : ctxt)
  _ -> Nothing

-- | Empty context
empty :: Ctxt a
empty = []

-- | Replace the first occurence of an item in a context
replace :: Ctxt a -> Id -> a -> Ctxt a
replace [] name v
  = [(name, v)]
replace ((name', _):ctxt) name v | name == name'
  = (name', v) : ctxt
replace (x : ctxt) name v
  = x : replace ctxt name v

-- | Map over the just elements of the context (and not the keys (identifiers))
ctxtMap :: (a -> b) -> Ctxt a -> Ctxt b
ctxtMap f [] = []
ctxtMap f ((v, x):ctxt) = (v, f x) : ctxtMap f ctxt

-- $setup
-- >>> import Language.Granule.Syntax.Identifiers (mkId)
{- | Take the intersection of two contexts based on keys
NOTE: this is not a commutative action, consider:
>>> intersectCtxts [(mkId "x",1)] [(mkId "x",2)]
[((Id "x" "x"),1)]
-}
intersectCtxts :: Ctxt a -> Ctxt a -> Ctxt a
intersectCtxts a b = normaliseCtxt $ filter (appearsIn b) a
  where appearsIn x (name, _) = isJust $ lookup name x

intersectCtxtsAlternatives :: Eq a => Ctxt a -> Ctxt a -> Ctxt (a, a)
intersectCtxtsAlternatives a b =
    [(k1, (v1, v2)) | (k1, v1) <- a, (k2, v2) <- b, k1 == k2, v1 /= v2]

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

deleteVars :: Ctxt t -> [Id] -> Ctxt t
deleteVars = foldr deleteVar

relevantSubCtxt :: [Id] -> Ctxt t -> Ctxt t
relevantSubCtxt vars = filter relevant
  where relevant (var, _) = var `elem` vars

lookupAndCutout :: Id -> Ctxt t -> Maybe (Ctxt t, t)
lookupAndCutout _ [] = Nothing
lookupAndCutout v ((v', t):ctxt) | v == v' =
   Just (ctxt, t)
lookupAndCutout v ((v', t'):ctxt) = do
  (ctxt', t) <- lookupAndCutout v ctxt
  Just ((v', t') : ctxt', t)

getCtxtIds :: Ctxt t -> [Id]
getCtxtIds = map fst
