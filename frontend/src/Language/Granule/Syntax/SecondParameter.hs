{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Language.Granule.Syntax.SecondParameter where

import GHC.Generics

class SecondParameter a e | a -> e where
  getSecondParameter :: a -> e
  setSecondParameter :: e -> a -> a

  default getSecondParameter :: (Generic a, GSecondParameter (Rep a) e) => a -> e
  getSecondParameter a = getSecondParameter' . from $ a

  default setSecondParameter :: (Generic a, GSecondParameter (Rep a) e) => e -> a -> a
  setSecondParameter e a = to . setSecondParameter' e . from $ a

class GSecondParameter f e where
  getSecondParameter' :: f a -> e
  setSecondParameter' :: e -> f a -> f a

instance {-# OVERLAPPABLE #-} GSecondParameter (K1 i a) e where
  getSecondParameter' _ = undefined
  setSecondParameter' _ _ = undefined

instance GSecondParameter a e => GSecondParameter (M1 i c a) e where
  getSecondParameter' (M1 a) = getSecondParameter' a
  setSecondParameter' e (M1 a) = M1 $ setSecondParameter' e a

instance (GSecondParameter a e, GSecondParameter b e) => GSecondParameter (a :+: b) e where
  getSecondParameter' (L1 a) = getSecondParameter' a
  getSecondParameter' (R1 a) = getSecondParameter' a

  setSecondParameter' e (L1 a) = L1 $ setSecondParameter' e a
  setSecondParameter' e (R1 a) = R1 $ setSecondParameter' e a

instance (ParameterLeaf a, GSecondParameter a e, GSecondParameter' b e) => GSecondParameter (a :*: b) e where
  getSecondParameter' (a :*: b) =
    if isLeaf a
    then getSecondParameter'' b
    else getSecondParameter' a

  setSecondParameter' e (a :*: b) =
    if isLeaf a
    then a :*: setSecondParameter'' e b
    else setSecondParameter' e a :*: b

class GSecondParameter' f e where
  getSecondParameter'' :: f a -> e
  setSecondParameter'' :: e -> f a -> f a

instance GSecondParameter' a e => GSecondParameter' (M1 i c a) e where
  getSecondParameter'' (M1 a) = getSecondParameter'' a
  setSecondParameter'' e (M1 a) = M1 $ setSecondParameter'' e a

instance GSecondParameter' a e => GSecondParameter' (a :*: b) e where
  getSecondParameter'' (a :*: _) = getSecondParameter'' a
  setSecondParameter'' e (a :*: b) = setSecondParameter'' e a :*: b

instance {-# OVERLAPPING #-} GSecondParameter' (K1 i e) e where
  getSecondParameter'' (K1 a) = a
  setSecondParameter'' e (K1 _) = K1 e

instance {-# OVERLAPPABLE #-} GSecondParameter' (K1 i a) e where
  getSecondParameter'' _ = undefined
  setSecondParameter'' _ _  = undefined

class ParameterLeaf f where
  isLeaf :: f a -> Bool

instance ParameterLeaf (M1 i c a) where
  isLeaf _ = True

instance ParameterLeaf (a :*: b) where
  isLeaf _ = False
