module Language.Granule.Codegen.CodegenSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test
import Test.QuickCheck
import Language.Granule.Codegen.Codegen

spec :: Test.Spec
spec = do
  describe "Compiler Test"
    $ it "" $ True `shouldBe` True
--    $ it "is not commutative"
--    $ property (\e1 e2 -> intersectCtxts e1 e2 /= intersectCtxts e2 e1)
