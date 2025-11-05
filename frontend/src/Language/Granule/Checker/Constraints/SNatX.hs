{-# OPTIONS_GHC -fno-warn-missing-methods #-}

{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Represents the extended natural numbers in the solver
module Language.Granule.Checker.Constraints.SNatX where

-- import Control.Monad ((<=<))
import Data.SBV
import GHC.Generics (Generic)

newtype SNatX = SNatX { xVal  :: SInteger }
  deriving (Generic, Mergeable)

instance Show SNatX where
  show (SNatX val) = case unliteral val of
    Just (-1) -> "∞"
    Just n    -> show n
    _         -> "<symbolic>"

inf :: SNatX
inf = SNatX $ (literal (-1))

isInf :: SNatX -> SBool
isInf (SNatX n) = n .== -1

instance Num SNatX where
  x + y = ite (isInf x .|| isInf y)
              inf
              (SNatX (xVal x + xVal y))
  x * y = ite ((isInf x .&& y ./= 0) .|| (isInf y .&& x ./= 0)) -- 0 * ∞ = ∞ * 0 = 0
              inf
              (SNatX (xVal x * xVal y))
  x - y = ite (isInf x .|| isInf y)  -- ???
              inf
              (ite (x .< y)          -- monus
                   0
                   (SNatX (xVal x - xVal y)))
  fromInteger = SNatX . literal

instance EqSymbolic SNatX where
  (SNatX a) .== (SNatX b) = a .== b

instance OrdSymbolic SNatX where
  a .< b = ite (isInf b) (ite (isInf a) sFalse sTrue)
         $ ite (isInf a) sFalse
         $ xVal a .< xVal b

representationConstraint :: SInteger -> SBool
representationConstraint v = v .>= -1
