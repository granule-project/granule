module Syntax.ExprSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test

import Syntax.Expr
import Syntax.Helpers
import Syntax.Identifiers
import Syntax.Pattern
import Syntax.Span

spec :: Test.Spec
spec = do
  describe "Expression helpers" $
    it "free variable test" $
      freeVars (Val nullSpan ()
            (Abs () (PVar nullSpan () $ mkId "x") Nothing
              (Val nullSpan ()
                (Abs () (PVar nullSpan () $ mkId "y") Nothing
                  (Val nullSpan () (Var () $ mkId "z")))))) `shouldBe` [mkId "z"]
