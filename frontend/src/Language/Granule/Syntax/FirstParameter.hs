{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Language.Granule.Syntax.FirstParameter where

import GHC.Generics

class FirstParameter a e | a -> e where
  getFirstParameter :: a -> e
  setFirstParameter :: e -> a -> a

  default getFirstParameter :: (Generic a, GFirstParameter (Rep a) e) => a -> e
  getFirstParameter a = getFirstParameter' . from $ a

  default setFirstParameter :: (Generic a, GFirstParameter (Rep a) e) => e -> a -> a
  setFirstParameter e a = to . setFirstParameter' e . from $ a

class GFirstParameter f e where
  getFirstParameter' :: f a -> e
  setFirstParameter' :: e -> f a -> f a

instance {-# OVERLAPPING #-} GFirstParameter (K1 i e) e where
  getFirstParameter' (K1 a) = a
  setFirstParameter' e (K1 _)  = K1 e

instance {-# OVERLAPPABLE #-} GFirstParameter (K1 i a) e where
  getFirstParameter' _ = undefined
  setFirstParameter' _ _ = undefined

instance GFirstParameter a e => GFirstParameter (M1 i c a) e where
  getFirstParameter' (M1 a) = getFirstParameter' a
  setFirstParameter' e (M1 a) = M1 $ setFirstParameter' e a

instance (GFirstParameter a e, GFirstParameter b e) => GFirstParameter (a :+: b) e where
  getFirstParameter' (L1 a) = getFirstParameter' a
  getFirstParameter' (R1 a) = getFirstParameter' a

  setFirstParameter' e (L1 a) = L1 $ setFirstParameter' e a
  setFirstParameter' e (R1 a) = R1 $ setFirstParameter' e a

instance GFirstParameter a e => GFirstParameter (a :*: b) e where
  getFirstParameter' (a :*: _) = getFirstParameter' a
  setFirstParameter' e (a :*: b) = (setFirstParameter' e a :*: b)

instance (GFirstParameter U1 String) where
  getFirstParameter' _ = ""
  setFirstParameter' _ e = e
