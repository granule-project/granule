module Syntax.ExprSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test

import Syntax.Expr

spec :: Test.Spec
spec = do
  describe "Expression helpers" $
    it "free variable test" $
      freeVars (Val nullSpan
            (Abs (mkId "x") Nothing
              (Val nullSpan
                (Abs (mkId "y") Nothing
                  (Val nullSpan (Var $ mkId "z")))))) `shouldBe` [mkId "z"]
