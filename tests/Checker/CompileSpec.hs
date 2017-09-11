module Checker.CompileSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test
import Test.QuickCheck

import Checker.Compile
import Checker.Types
import Syntax.Expr

-- TODO: better arbitrary instances
instance Arbitrary Coeffect where
  arbitrary = do
    return $ CVar ""

instance Arbitrary CKind where
  arbitrary = do
    return $ CConstr "Nat"

instance Arbitrary SCoeffect where


spec :: Test.Spec
spec = do
  describe "compiling tests" $
    it "compilation of + is associative" $
        property $ (\c1 c2 c3 k vars -> compile (CPlus c1 (CPlus c2 c3)) k vars
                                     == compile (CPlus (CPlus c1 c2) c3) k vars)