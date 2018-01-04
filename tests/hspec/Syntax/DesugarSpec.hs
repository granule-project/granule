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
     (evalState (desugarPattern (mkId "v")
        (PBox nullSpan (PVar nullSpan (mkId "v1"))) (Box undefined (TyCon $ mkId "Int"))) 0 $
        (Val nullSpan $ Var $ mkId "v1"))
      `shouldBe`
       -- letBox |evalV0| : Int = v in case (v1, v2) -> v
        (LetBox nullSpan (mkId "v1") (TyCon $ mkId "Int")
           (Val nullSpan $ Var $ mkId "v")
             (Val nullSpan $ Var $ mkId "v1"))

    it "test nested box pair pattern" $
     (evalState (desugarPattern (mkId "v")
        (PBox nullSpan (PPair nullSpan (PVar nullSpan (mkId "v1")) (PVar nullSpan (mkId "v2"))))
        (Box undefined (PairTy (TyCon $ mkId "Int") (TyCon $ mkId "Int")))) 0 $
        (Val nullSpan $ Var $ mkId "v1"))
      `shouldBe`
       -- letBox |evalV0| : Int = v in case (v1, v2) -> v
        (LetBox nullSpan (mkId "eval v0") (PairTy (TyCon $ mkId "Int") (TyCon $ mkId "Int"))
           (Val nullSpan $ Var $ mkId "v")
             (Case nullSpan (Val nullSpan $ Var $ mkId "eval v0")
               [(PPair nullSpan (PVar nullSpan (mkId "v1")) (PVar nullSpan
                (mkId "v2")), Val nullSpan $ Var $ mkId "v1")]))
