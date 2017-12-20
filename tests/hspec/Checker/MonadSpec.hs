module Checker.MonadSpec where

import Test.Hspec

import Syntax.Expr
import Checker.Monad
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Control.Monad.Reader.Class
import Checker.Constraints
import Checker.Predicates
import Checker.LaTeX

spec :: Spec
spec = do
  -- Unit tests
  localCheckingSpec

  -- describe "" $ it "" $ True `shouldBe` True


localCheckingSpec :: Spec
localCheckingSpec = do
    describe "Unit tests on localised checking function" $ do
      it "Updates do not leak" $ do
        (Just (out, local), state) <- localising
        -- State hasn't been changed by the local context
        state `shouldBe` endStateExpectation
        out   `shouldBe` (Just "x10")
        (_, localState) <- runChecker endStateExpectation [] (runMaybeT local)
        localState `shouldBe` (transformState endStateExpectation)

  where
    endStateExpectation = initState { uniqueVarId = 10 }
    localising = runChecker initState [] $ runMaybeT $ do
      state <- get
      put (state { uniqueVarId = 10 })
      localChecking $ do
        state <- get
        put (transformState state)
        return $ "x" ++ show (uniqueVarId state)
    transformState st =
      st { uniqueVarId  = 1 + uniqueVarId st
         , tyVarContext = [("inner", (KType, ForallQ))]
         , kVarContext  = [("innerk", KType)]
         , deriv        = Just $ Leaf "testing"
         , derivStack   = [Leaf "unit test"] }