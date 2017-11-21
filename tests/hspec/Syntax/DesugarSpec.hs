module Syntax.DesugarSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test

import Syntax.Desugar
import Syntax.Expr
import Control.Monad.State.Strict

spec :: Test.Spec
spec = do
  describe "Desugaring patterns" $ do

    it "test nested box variable pattern" $
     (evalState (desugarPattern "v"
        (PBox nullSpan (PVar nullSpan "v1")) (Box undefined (TyCon "Int"))) 0 $
        (Val nullSpan $ Var "v1"))
      `shouldBe`
       -- letBox |evalV0| : Int = v in case (v1, v2) -> v
        (LetBox nullSpan "v1" (TyCon "Int")
           (Val nullSpan $ Var "v")
             (Val nullSpan $ Var "v1"))

    it "test nested box pair pattern" $
     (evalState (desugarPattern "v"
        (PBox nullSpan (PPair nullSpan (PVar nullSpan "v1") (PVar nullSpan "v2")))
        (Box undefined (PairTy (TyCon "Int") (TyCon "Int")))) 0 $
        (Val nullSpan $ Var "v1"))
      `shouldBe`
       -- letBox |evalV0| : Int = v in case (v1, v2) -> v
        (LetBox nullSpan "eval v0" (PairTy (TyCon "Int") (TyCon "Int"))
           (Val nullSpan $ Var "v")
             (Case nullSpan (Val nullSpan $ Var "eval v0")
               [(PPair nullSpan (PVar nullSpan "v1") (PVar nullSpan
               "v2"), Val nullSpan $ Var "v1")]))