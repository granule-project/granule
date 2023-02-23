module Language.Granule.Synthesis.SynthSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test

import Language.Granule.Synthesis.Common
import Language.Granule.Synthesis.Monad
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
import Language.Granule.Checker.Monad(initState)
import Language.Granule.Utils

import Control.Monad.State.Strict

-- To run just these tests do: stack test --test-arguments "-m "Synth""

spec :: Test.Spec
spec = let ?globals = mempty :: Globals in do
  describe "Tests on checkConstructor" $ do
    it "Monomorphic tests" $ do
      -- A unit constructor matches a unit goal
      constr <- testSynthesiser
                   $ checkConstructor False (Forall ns [] [] (TyCon (mkId "()"))) (TyCon (mkId "()")) []
      let status = map (fmap (\(status, _, _, _, _) -> status)) constr
      status `shouldBe` [Just True]

testSynthesiser :: (?globals :: Globals) => Synthesiser a -> IO [Maybe a]
testSynthesiser m = do
    (outputs, _) <- runStateT (runSynthesiser 0 m initState) mempty
    return $ map (convertError . fst) outputs
  where
    convertError (Right a) = Just a
    convertError (Left _)  = Nothing