{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}

module Language.Granule.Checker.Constraints.SymbolicGrades where

{- Provides a symbolic representation of grades (coeffects, effects, indices)
   in order for a solver to use.
-}

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Checker.Constraints.SNatX (SNatX(..))

import GHC.Generics (Generic)
import Data.SBV hiding (kindOf, name, symbolic)
import qualified Data.Set as S

-- Symbolic grades, for coeffects and indices
data SGrade =
       SNat      SInteger
     | SFloat    SFloat
     | SLevel    SInteger
     | SSet      (S.Set (Id, Type))
     | SExtNat   SNatX
     | SInterval { sLowerBound :: SGrade, sUpperBound :: SGrade }
     -- Single point coeffect (not exposed at the moment)
     | SPoint
    deriving (Show, Generic)

natLike :: SGrade -> Maybe SInteger
natLike (SNat x) = Just x
natLike (SExtNat (SNatX x)) = Just x
natLike _ = Nothing

instance Mergeable SGrade where
  symbolicMerge s sb (SNat n) (SNat n') = SNat (symbolicMerge s sb n n')
  symbolicMerge s sb (SFloat n) (SFloat n') = SFloat (symbolicMerge s sb n n')
  symbolicMerge s sb (SLevel n) (SLevel n') = SLevel (symbolicMerge s sb n n')
  symbolicMerge s sb (SSet n) (SSet n') = error "Can't symbolic merge sets yet"
  symbolicMerge s sb (SExtNat n) (SExtNat n') = SExtNat (symbolicMerge s sb n n')
  symbolicMerge s sb (SInterval lb1 ub1) (SInterval lb2 ub2) =
    SInterval (symbolicMerge s sb lb1 lb2) (symbolicMerge s sb ub1 ub2)
  symbolicMerge s sb SPoint SPoint = SPoint

instance OrdSymbolic SGrade where
  (SInterval lb1 ub1) .< (SInterval lb2 ub2) =
    lb2 .< lb1 &&& ub1 .< ub2
  (SNat n)    .< (SNat n') = n .< n'
  (SFloat n)  .< (SFloat n') = n .< n'
  (SLevel n)  .< (SLevel n') = n .< n'
  (SSet n)    .< (SSet n') = error "Can't compare symbolic sets yet"
  (SExtNat n) .< (SExtNat n') = n .< n'
  SPoint .< SPoint = true

instance EqSymbolic SGrade where
  (SInterval lb1 ub1) .== (SInterval lb2 ub2) =
    lb2 .== lb1 &&& ub1 .== ub2
  (SNat n)    .== (SNat n') = n .== n'
  (SFloat n)  .== (SFloat n') = n .== n'
  (SLevel n)  .== (SLevel n') = n .== n'
  (SSet n)    .== (SSet n') = error "Can't compare symbolic sets yet"
  (SExtNat n) .== (SExtNat n') = n .== n'
  SPoint .== SPoint = true

-- | Meet operation on symbolic grades
symGradeMeet :: SGrade -> SGrade -> SGrade
symGradeMeet (SNat n1) (SNat n2)     = SNat $ n1 `smin` n2
symGradeMeet (SSet s) (SSet t)       = SSet $ S.intersection s t
symGradeMeet (SLevel s) (SLevel t)   = SLevel $ s `smin` t
symGradeMeet (SFloat n1) (SFloat n2) = SFloat $ n1 `smin` n2
symGradeMeet (SExtNat x) (SExtNat y) = SExtNat (x `smin` y)
symGradeMeet (SInterval lb1 ub1) (SInterval lb2 ub2) =
  SInterval (lb1 `symGradeMeet` lb2) (ub1 `symGradeMeet` ub2)
symGradeMeet SPoint SPoint = SPoint

-- | Join operation on symbolic grades
symGradeJoin :: SGrade -> SGrade -> SGrade
symGradeJoin (SNat n1) (SNat n2) = SNat (n1 `smax` n2)
symGradeJoin (SSet s) (SSet t)   = SSet $ S.intersection s t
symGradeJoin (SLevel s) (SLevel t) = SLevel $ s `smax` t
symGradeJoin (SFloat n1) (SFloat n2) = SFloat (n1 `smax` n2)
symGradeJoin (SExtNat x) (SExtNat y) = SExtNat (x `smax` y)
symGradeJoin (SInterval lb1 ub1) (SInterval lb2 ub2) =
   SInterval (lb1 `symGradeJoin` lb2) (ub1 `symGradeJoin` ub2)
symGradeJoin SPoint SPoint = SPoint

-- | Plus operation on symbolic grades
symGradePlus :: SGrade -> SGrade -> SGrade
symGradePlus (SNat n1) (SNat n2) = SNat (n1 + n2)
symGradePlus (SSet s) (SSet t) = SSet $ S.union s t
symGradePlus (SLevel lev1) (SLevel lev2) = SLevel $ lev1 `smax` lev2
symGradePlus (SFloat n1) (SFloat n2) = SFloat $ n1 + n2
symGradePlus (SExtNat x) (SExtNat y) = SExtNat (x + y)
symGradePlus (SInterval lb1 ub1) (SInterval lb2 ub2) =
    SInterval (lb1 `symGradePlus` lb2) (ub1 `symGradePlus` ub2)
symGradePlus SPoint SPoint = SPoint

-- | Times operation on symbolic grades
symGradeTimes :: SGrade -> SGrade -> SGrade
symGradeTimes (SNat n1) (SNat n2) = SNat (n1 * n2)
symGradeTimes (SSet s) (SSet t) = SSet $ S.union s t
symGradeTimes (SLevel lev1) (SLevel lev2) = SLevel $ lev1 `smin` lev2
symGradeTimes (SFloat n1) (SFloat n2) = SFloat $ n1 * n2
symGradeTimes (SExtNat x) (SExtNat y) = SExtNat (x * y)
symGradeTimes (SInterval lb1 ub1) (SInterval lb2 ub2) =
    SInterval (lb1 `symGradeTimes` lb2) (ub1 `symGradeTimes` ub2)
symGradeTimes SPoint SPoint = SPoint
