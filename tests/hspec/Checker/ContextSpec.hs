module Checker.ContextSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test

spec :: Test.Spec
spec = do
  describe "" $ it "" $ True `shouldBe` True

{-
spec :: Test.Spec
spec = do
  describe ""
-}
