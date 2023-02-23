module Language.Granule.Synthesis.CommonSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test

import Language.Granule.Synthesis.Common
import Language.Granule.Synthesis.Monad
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
import Language.Granule.Checker.Checker(checkDataCons,checkTyCon)
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Checker.Monad(initState,runAll)
import Language.Granule.Utils

import Control.Monad.State.Strict

-- To run just these tests do:
--  stack test granule-frontend --test-arguments "-m "Common""

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
testSynthesiser synthComputation = do
    -- Load in the primitive data constructors first before running the computation synthComputation
    let synthComputation' =
             (conv (runAll checkTyCon Primitives.dataTypes))
          >> (conv (runAll checkDataCons Primitives.dataTypes))
          >> synthComputation
    (outputs, dat) <- runStateT (runSynthesiser 1 synthComputation' initState) mempty
    mapM (convertError . fst) outputs
  where
    convertError (Right a) = return $ Just a
    convertError (Left err) = do
      -- Print error message if something went badly wrong
      putStrLn $ show err
      return $ Nothing