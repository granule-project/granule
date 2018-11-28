module Language.Granule.Checker.Constraints.Quantifiable where

import Language.Granule.Checker.Constraints.SNatX
import Data.SBV hiding (kindOf, name, symbolic)

-- | Represents symbolic values which can be quantified over inside the solver
-- | Mostly this just overrides to SBV's in-built quantification, but sometimes
-- | we want some custom things to happen when we quantify
class Quantifiable a where
  universal :: String -> Symbol (SBV a)
  existential :: String -> Symbol (SBV a)

instance Quantifiable SInteger where
  universal = forall
  existential = exists

instance Quantifiable SNatX where
  universal = forallSNatX
  existential = existsSNatX
