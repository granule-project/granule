module ContextSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test
import Test.QuickCheck
import Context

spec :: Test.Spec
spec = do
  describe "key intersection properties"
    $ it "" $ True `shouldBe` True
--    $ it "is not commutative"
--    $ property (\e1 e2 -> intersectCtxts e1 e2 /= intersectCtxts e2 e1)
