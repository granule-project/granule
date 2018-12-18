{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}

{- This module contains some recursion schemes designed for use with mutually
   recursive ADT bifunctors.

   Taking ideas from the recursion-shemes package which defines recursion schemes
   for recursive functors we define cata and cataM for mutually
   recursive bifunctors.

   The approach is based on ideas from:
   1. 'Generic Programming with Fixed Points for Mutually Recursive Datatypes' available at
      http://users.eecs.northwestern.edu/~clk800/rand-test-study/_gpwfpfmrd/gpwfpfmrd-2009-10-8-12-02-00.pdf
   2. 'Designing and Implementing Combinator Languages' available at
      http://www.staff.science.uu.nl/~swier101/Papers/1999/AFP3.pdf -}
module Data.Bifunctor.Foldable where

import Data.Bifunctor
import Data.Bitraversable
import Control.Monad ((<=<))

newtype Fix2 f g = Fix2 { unFix :: (f (Fix2 f g) (Fix2 g f)) }

-- The base functor of two mutually recurive fixed points
type family Base t q :: (* -> * -> *)
type instance Base (Fix2 f g) (Fix2 g f) = f

instance (Bifunctor f, Bifunctor g) => Birecursive (Fix2 f g) (Fix2 g f) where
    project = unFix

instance Show (f (Fix2 f g) (Fix2 g f)) => Show (Fix2 f g) where
    showsPrec n x = showsPrec 11 (unFix x)
    -- NOTE: For readablity the Fix2 constructor is intentionally not shown.

instance Eq (f (Fix2 f g) (Fix2 g f)) => Eq (Fix2 f g) where
    a == b = (unFix a) == (unFix b)

class (Bifunctor (Base t q)) => Birecursive t q | t -> q where
    project :: t -> (Base t q) t q

bicata :: (Birecursive x z, Birecursive z x)
       => (Bifunctor (Base x z), Bifunctor (Base z x))
       => ((Base x z) a b -> a)
       -> ((Base z x) b a -> b)
       -> x
       -> a
bicata falg galg =
    fcata
    where fcata = falg . (bimap fcata gcata) . project
          gcata = galg . (bimap gcata fcata) . project

bicataM :: (Birecursive x z, Birecursive z x)
        => (Bitraversable (Base x z), Bitraversable (Base z x))
        => (Monad m)
        => ((Base x z) a b -> m a)
        -> ((Base z x) b a -> m b)
        -> x
        -> m a
bicataM falgM galgM =
    fcataM
    where fcataM = falgM <=< (bimapM fcataM gcataM) . project
          gcataM = galgM <=< (bimapM gcataM fcataM) . project
