{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Represents extended coeffects.
module Language.Granule.Checker.Constraints.SExt
  (
   -- * Extended coeffects.
    SExt
  , pattern SExtUn
  , pattern SExtX
  , isExt
  , extBase

  -- * Top-completed coeffects.
  , TopCompleted
  , isTop
  , notTop
  , HasTop(..)

  -- * Semirings
  , Semiring(..)
  , Tropical

  -- * Helpers
  , FromSInteger(..)
  ) where


import Data.Either (isRight)
import Data.SBV


import Language.Granule.Checker.Constraints.Semiring


-- | Base @b@, extension type @e@.
newtype SExt b e = SExt { unExt :: Either b e }
  deriving (EqSymbolic, Mergeable)


pattern SExtUn :: b -> SExt b e
pattern SExtUn b = SExt (Left b)

pattern SExtX :: e -> SExt b e
pattern SExtX e = SExt (Right e)


instance (Show b, Show e) => Show (SExt b e) where
  show = either show show . unExt


isExt :: SExt b e -> Bool
isExt = isRight . unExt


extBase :: b -> SExt b e
extBase = SExtUn


extWith :: e -> SExt b e
extWith = SExtX


exts :: (b -> e -> c) ->
        (e -> b -> c) ->
        (b -> b -> c) ->
        (e -> e -> c) ->
        SExt b e -> SExt b e -> c
exts lr rl ll rr x y = either (\b -> either (ll b) (lr b) (unExt y))
                                 (\e -> either (rl e) (rr e) (unExt y)) (unExt x)


const2 :: c -> a -> b -> c
const2 x _ _ = x


newtype Top = Top ()
  deriving (Mergeable)


instance EqSymbolic Top where
  (Top ()) .== (Top ()) = sTrue


instance Show Top where
  show _ = "∞"


type TopCompleted a = SExt a Top


instance HasTop (TopCompleted b) where
  top = extWith (Top ())


notTop :: b -> TopCompleted b
notTop = extBase


isTop :: TopCompleted b -> Bool
isTop = isExt


isZero :: (EqSymbolic a, Semiring a) => a -> SBool
isZero = ((.==) zero)


instance (OrdSymbolic b) => OrdSymbolic (TopCompleted b) where
  x .< y = exts (const2 sTrue) (const2 sFalse) (\a b -> a .< b) (const2 sFalse) x y


-----------------------
-- Tropical Semiring --
-----------------------


newtype Tropical = Tropical { unTropical :: TopCompleted SInteger }
  deriving (Show, EqSymbolic, HasTop, Mergeable, OrdSymbolic)


instance Semiring Tropical where
  zero = Tropical top
  one  = Tropical (notTop 0)
  plus x y =
    Tropical $ exts (\b _ -> extBase b) (\_ b -> extBase b) (\a b -> extBase (smin a b)) (const2 top) (unTropical x) (unTropical y)

  times x y = ite (isZero x .|| isZero y) zero
        (Tropical $ (exts (const2 top) (const2 top) (\a b -> extBase (a + b)) (const2 top) (unTropical x) (unTropical y)))


instance FromSInteger Tropical where
  fromSInteger = Tropical . extBase


-------------------
----- Helpers -----
-------------------


class FromSInteger a where
  fromSInteger :: SInteger -> a


class HasTop a where
  top :: a
