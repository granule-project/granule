module Checker.TypesSpec where

import Test.Hspec
import Checker.Types
import Context

spec :: Spec
spec = do
  describe "environment handling" $
    it "Replacing replaces only one occurence" $
      replace [("x", 1), ("y", 2), ("x", 3)] "x" 0 `shouldBe` [("x", 0), ("y", 2), ("x", 3)]