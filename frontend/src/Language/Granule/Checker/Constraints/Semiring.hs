-- | Represents extended coeffects.
module Language.Granule.Checker.Constraints.Semiring
  (
  -- * Semirings
    Semiring(..)
  ) where


class Semiring a where
  zero :: a
  one  :: a
  plus :: a -> a -> a
  times :: a -> a -> a
