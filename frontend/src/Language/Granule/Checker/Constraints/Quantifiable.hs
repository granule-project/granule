{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Granule.Checker.Constraints.Quantifiable where

import Language.Granule.Checker.Constraints.SNatX
import Data.SBV

-- | Represents symbolic values which can be quantified over inside the solver
-- | Mostly this just overrides to SBV's in-built quantification, but sometimes
-- | we want some custom things to happen when we quantify
class Quantifiable a where
  universal :: String -> Symbolic a
  existential :: String -> Symbolic a

class QuantifiableScoped a where
  universalScoped :: String -> (SBV a -> Symbolic SBool) -> Symbolic SBool
  existentialScoped :: String -> (SBV a -> Symbolic SBool) -> Symbolic SBool

instance Quantifiable SInteger where
  universal = forall
  existential = exists

instance QuantifiableScoped Integer where
  universalScoped v = forAll [v]
  existentialScoped v = forAll [v]

instance Quantifiable SFloat where
  universal = forall
  existential = exists

instance QuantifiableScoped Float where
  universalScoped v = forAll [v]
  existentialScoped v = forAll [v]

instance Quantifiable SNatX where
  universal = forallSNatX
  existential = existsSNatX
