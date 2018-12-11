#!/usr/bin/env stack
{- stack script
  --resolver nightly-2018-11-24
-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE KindSignatures #-}

import Data.Kind (Type)

data (:==:) (a :: Type) :: Type -> Type where
  Refl :: a :==: a

sym :: x :==: y -> y :==: x
sym Refl = Refl

trans :: x :==: y -> y :==: z -> x :==: y
trans Refl Refl = Refl

cong :: Functor f => x :==: y -> f x :==: f y
cong Refl = Refl



main = putStrLn "ok"
