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

import Data.Bifunctor hiding (second)
import Data.Bitraversable
import Control.Monad ((<=<))
import Data.Kind

newtype Fix2 f g = Fix2 { unFix :: (f (Fix2 f g) (Fix2 g f)) }

-- The base functor of two mutually recurive fixed points
type family Base t q :: (Type -> Type -> Type)
type instance Base (Fix2 f g) (Fix2 g f) = f

instance Show (f (Fix2 f g) (Fix2 g f)) => Show (Fix2 f g) where
    showsPrec n x = showsPrec 11 (unFix x)
    -- NOTE: For readablity the Fix2 constructor is intentionally not shown.

instance Eq (f (Fix2 f g) (Fix2 g f)) => Eq (Fix2 f g) where
    a == b = (unFix a) == (unFix b)

class (Bifunctor (Base t q)) => Birecursive t q | t -> q where
    project :: t -> (Base t q) t q

instance (Bifunctor f) => Birecursive (Fix2 f g) (Fix2 g f) where
    project = unFix

bicata :: (Birecursive x z, Birecursive z x)
       => ((Base x z) a b -> a)
       -> ((Base z x) b a -> b)
       -> x
       -> a
bicata falg galg =
    fcata
    where fcata = falg . (bimap fcata gcata) . project
          gcata = galg . (bimap gcata fcata) . project

bicataP :: (Birecursive x z, Birecursive z x)
       => ((p -> (Base x z) a b -> a), x -> p -> p)
       -> ((p -> (Base z x) b a -> b), z -> p -> p)
       -> p
       -> x
       -> a
bicataP (falgP, ftop) (galgP, gtop) =
    fcataP
    where fcataP p fp =
            let p' = ftop fp p
            in falgP p' $ bimap (fcataP p') (gcataP p') $ project fp
          gcataP p fp =
            let p' = gtop fp p
            in galgP p' $ bimap (gcataP p') (fcataP p') $ project fp

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

bicataPM :: (Birecursive x z, Birecursive z x)
         => (Bitraversable (Base x z), Bitraversable (Base z x))
         => (Monad m)
         => ((p -> (Base x z) a b -> m a), x -> p -> p)
         -> ((p -> (Base z x) b a -> m b), z -> p -> p)
         -> p
         -> x
         -> m a
bicataPM (falgPM, ftop) (galgPM, gtop) =
    fcataPM
    where fcataPM p fp =
            let p' = ftop fp p
            in (bimapM (fcataPM p') (gcataPM p') $ project fp) >>= falgPM p'
          gcataPM p fp =
            let p' = gtop fp p
            in (bimapM (gcataPM p') (fcataPM p') $ project fp) >>= galgPM p'

bipara :: (Birecursive x z, Birecursive z x)
       => ((Base x z) (x, a) (z, b) -> a)
       -> ((Base z x) (z, b) (x, a) -> b)
       -> x
       -> a
bipara falg galg =
    fpara
    where fpara =
            falg . (bimap ((,) <*> fpara) ((,) <*> gpara)) . project
          gpara =
            galg . (bimap ((,) <*> gpara) ((,) <*> fpara)) . project

applyLeft :: Functor f => (a -> f b) -> a -> f (a, b)
applyLeft f x = (,) x <$> f x

biparaP :: (Birecursive x z, Birecursive z x)
       => ((p -> (Base x z) (x, a) (z, b) -> a), x -> p -> p)
       -> ((p -> (Base z x) (z, b) (x, a) -> b), z -> p -> p)
       -> p
       -> x
       -> a
biparaP (falgP, ftop) (galgP, gtop) =
    fparaP
    where fparaP p fp =
            let p' = ftop fp p
            in falgP p' $ bimap ((,) <*> (fparaP p')) ((,) <*> (gparaP p')) $ project fp
          gparaP p fp =
            let p' = gtop fp p
            in galgP p' $ bimap ((,) <*> (gparaP p')) ((,) <*> (fparaP p')) $ project fp

biparaM :: (Birecursive x z, Birecursive z x)
        => (Bitraversable (Base x z), Bitraversable (Base z x))
        => (Monad m)
        => ((Base x z) (x, a) (z, b) -> m a)
        -> ((Base z x) (z, b) (x, a) -> m b)
        -> x
        -> m a
biparaM falgM galgM =
    fparaM
    where fparaM = falgM <=< (bimapM (applyLeft fparaM) (applyLeft gparaM)) . project
          gparaM = galgM <=< (bimapM (applyLeft gparaM) (applyLeft fparaM)) . project

biparaPM :: (Birecursive x z, Birecursive z x)
         => (Bitraversable (Base x z), Bitraversable (Base z x))
         => (Monad m)
         => ((p -> (Base x z) (x, a) (z, b) -> m a), x -> p -> p)
         -> ((p -> (Base z x) (z, b) (x, a) -> m b), z -> p -> p)
         -> p
         -> x
         -> m a
biparaPM (falgPM, ftop) (galgPM, gtop) =
    fcataPM
    where fcataPM p fp =
            let p' = ftop fp p
            in ((bimapM (applyLeft $ fcataPM p') (applyLeft $ gcataPM p')) $ project fp) >>= falgPM p'
          gcataPM p fp =
            let p' = gtop fp p
            in ((bimapM (applyLeft $ gcataPM p') (applyLeft $ fcataPM p')) $ project fp) >>= galgPM p'
