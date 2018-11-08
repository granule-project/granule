module Language.Granule.Checker.TypesSpec where

import Language.Granule.Syntax.Identifiers
import Test.Hspec
import Language.Granule.Context

spec :: Spec
spec = do
  describe "context handling" $
    it "Replacing replaces only one occurence" $
      replace [(mkId "x", 1), (mkId "y", 2), (mkId "x", 3)] (mkId "x") 0
        `shouldBe` [(mkId "x", 0), (mkId "y", 2), (mkId "x", 3)]
