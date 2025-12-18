-- | Symbolic representation of semiring terms as syntax trees.
-- Used for doing some limited solving over polymorphic coeffect grades.
module Language.Granule.Checker.Constraints.SynTree
  ( SynTree(..)
  , normaliseSynTree
  , synTreeApproxEq
  ) where

import Data.SBV hiding (kindOf, name, symbolic)
import qualified Data.Text as T

-- | Representation of semiring terms as a `SynTree`
data SynTree =
    SynPlus SynTree SynTree
  | SynTimes SynTree SynTree
  | SynMeet SynTree SynTree
  | SynJoin SynTree SynTree
  | SynLeaf (Maybe SInteger) -- Just 0 represents the 0 of a semiring
                             -- Just n represents 1 + 1 + .... = n  (when n /= 0)
  | SynMerge SBool SynTree SynTree

-- | Performs some normalisation on a symbolic tree
normaliseSynTree :: SynTree -> SynTree
normaliseSynTree (SynPlus (SynLeaf (Just x)) (SynLeaf (Just y))) =
  SynLeaf (Just (x + y))
normaliseSynTree (SynTimes (SynLeaf (Just x)) (SynLeaf (Just y))) =
  SynLeaf (Just (x * y))
normaliseSynTree (SynPlus s t) = SynPlus (normaliseSynTree s) (normaliseSynTree t)
normaliseSynTree (SynTimes s t) = SynTimes (normaliseSynTree s) (normaliseSynTree t)
normaliseSynTree (SynMeet s t) = SynMeet (normaliseSynTree s) (normaliseSynTree t)
normaliseSynTree (SynJoin s t) = SynJoin (normaliseSynTree s) (normaliseSynTree t)
normaliseSynTree (SynMerge sb s t) = SynMerge sb (normaliseSynTree s) (normaliseSynTree t)
normaliseSynTree x = x

instance Show SynTree where
  show (SynPlus s t) = "(" ++ show s ++ " + " ++ show t ++ ")"
  show (SynTimes s t) = show s ++ " * " ++ show t
  show (SynJoin s t) = "(" ++ show s ++ " \\/ " ++ show t ++ ")"
  show (SynMeet s t) = "(" ++ show s ++ " /\\ " ++ show t ++ ")"
  show (SynLeaf Nothing) = "?"
  show (SynLeaf (Just n)) = T.unpack $
    T.replace (T.pack " :: SInteger") (T.pack "") (T.pack $ show n)
  show (SynMerge sb s t) = "(if " ++ show sb ++ " (" ++ show s ++ ") (" ++ show t ++ "))"

-- | Approximate equality check for SynTree
synTreeApproxEq :: SynTree -> SynTree -> SBool
synTreeApproxEq s t = normaliseSynTree s `synTreeApproxEq'` normaliseSynTree t

synTreeApproxEq' :: SynTree -> SynTree -> SBool
synTreeApproxEq' (SynPlus s s') (SynPlus t t') =
       -- + is commutative
      (synTreeApproxEq' s t .&& synTreeApproxEq' s' t') 
  .|| (synTreeApproxEq' s' t .&& synTreeApproxEq' s t')
synTreeApproxEq' (SynTimes s s') (SynTimes t t') =
   synTreeApproxEq' s t .&& synTreeApproxEq' s' t'
synTreeApproxEq' (SynMeet s s') (SynMeet t t')   =
  -- /\ is commutative
  (synTreeApproxEq' s t .&& synTreeApproxEq' s' t') .|| (synTreeApproxEq' s t' .&& synTreeApproxEq' s' t)
synTreeApproxEq' (SynJoin s s') (SynJoin t t')   =
  -- \/ is commutative
  (synTreeApproxEq' s t .&& synTreeApproxEq' s' t') .|| (synTreeApproxEq' s t' .&& synTreeApproxEq' s' t)
synTreeApproxEq' (SynMerge sb s s') (SynMerge sb' t t')  =
    ((synTreeApproxEq' s t .&& synTreeApproxEq' s' t') .&& (sb .== sb')) .||
    -- Flipped branching
    ((synTreeApproxEq' s t' .&& synTreeApproxEq' s t) .&& (sb .== sNot sb'))
synTreeApproxEq' (SynLeaf Nothing) (SynLeaf Nothing) = sFalse
synTreeApproxEq' (SynLeaf (Just n)) (SynLeaf (Just n')) = n .=== n'
-- ^^^ We should never compare for <= as `n` and `n'` are the free representation
-- of a semiring element formed by `0` or repeated addition of `1`. But we do 
-- not know for any arbitrary semiring whether we have any ordering between
-- any semiring elements, so we can only do equality.
synTreeApproxEq' _ _ = sFalse
