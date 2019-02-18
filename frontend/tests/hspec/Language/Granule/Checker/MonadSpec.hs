module Language.Granule.Checker.MonadSpec where

import Test.Hspec

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type

import Language.Granule.Checker.Monad
import Control.Monad.State.Strict
import Control.Monad.Reader.Class

import Data.Maybe (fromJust)
import qualified Data.Map as M

import Language.Granule.Checker.Constraints
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.LaTeX

spec :: Spec
spec = do
  -- Unit tests
  peekCheckerSpec

  -- describe "" $ it "" $ True `shouldBe` True

  -- peekChecker :: Checker a -> Checker (CheckerResult a, Checker ())

peekCheckerSpec :: Spec
peekCheckerSpec = do
    describe "Unit tests on localised checking function" $ do
      it "Updates do not leak" $ do
        (Right (Right out, local), state) <- localising
        -- State hasn't been changed by the local context
        state `shouldBe` endStateExpectation
        out   `shouldBe` "x10"
        (_, localState) <- runChecker endStateExpectation local
        localState `shouldBe` (transformState endStateExpectation)

  where
    endStateExpectation = initState { uniqueVarIdCounterMap = M.insert "x" 10 (M.empty) }
    localising :: IO (CheckerResult (CheckerResult String, Checker ()), CheckerState)
    localising = runChecker initState $ do
      state <- get
      put (state { uniqueVarIdCounterMap = M.insert "x" 10 (M.empty) })
      peekChecker $ do
        state <- get
        put (transformState state)
        return $ "x" <> show (fromJust $ M.lookup "x" (uniqueVarIdCounterMap state))
    transformState st =
      st { uniqueVarIdCounterMap  = M.insertWith (+) "x" 1 (uniqueVarIdCounterMap st)
         , tyVarContext = [(mkId "inner", (KType, ForallQ))]
         , kVarContext  = [(mkId "innerk", KType)]
         , deriv        = Just $ Leaf "testing"
         , derivStack   = [Leaf "unit test"] }
