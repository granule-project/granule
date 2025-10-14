{-# OPTIONS_GHC -fno-warn-missing-methods #-}

{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Represents fractions with star in the solver
module Language.Granule.Checker.Constraints.SFrac where

-- import Control.Monad ((<=<))
import Data.SBV
import GHC.Generics (Generic)

newtype SFrac = SFrac { fVal  :: SFloat }
  deriving (Generic, Mergeable)

instance Show SFrac where
  show (SFrac val) = case unliteral val of
    Just (0) -> "*"
    Just f    -> show f
    _         -> "<symbolic>"

star :: SFrac
star = SFrac $ (literal (0))

isUniq :: SFrac -> SBool
isUniq (SFrac f) = f .== 0

instance Num SFrac where
  x + y = ite (isUniq x .|| isUniq y)
              star
              (SFrac (fVal x + fVal y))
  x * y = ite (isUniq x .|| isUniq y)
              star
              (SFrac (fVal x * fVal y))
  x - y = ite (isUniq x .|| isUniq y)
              star
              (SFrac (fVal x - fVal y))

instance EqSymbolic SFrac where
  (SFrac a) .== (SFrac b) = a .== b

instance OrdSymbolic SFrac where
  (SFrac a) .< (SFrac b) = a .== b

fractionConstraint :: SFloat -> SBool
fractionConstraint v = v .== v .&& v .<= 1 .&& v .>= 0

freeSFrac :: String -> Symbolic SFrac
freeSFrac nm = do
  v <- sFloat $ nm <> "_fVal"
  constrain $ fractionConstraint v
  return $ SFrac v

existsSFrac :: String -> Symbolic SFrac
existsSFrac nm = do
  v <- free $ nm <> "_fVal"
  constrain $ \(Exists v) -> fractionConstraint v
  return $ SFrac v

forallSFrac :: String -> Symbolic SFrac
forallSFrac nm = do
  v <- free $ nm <> "_fVal"
  constrain $ \(Forall v) -> fractionConstraint v
  return $ SFrac v