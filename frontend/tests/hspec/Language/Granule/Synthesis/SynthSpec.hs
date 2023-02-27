module Language.Granule.Synthesis.SynthSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test

-- import Language.Granule.Synthesis.Common
-- import Language.Granule.Synthesis.Monad
-- import Language.Granule.Synthesis.Synth
-- import Language.Granule.Syntax.Def
-- import Language.Granule.Syntax.Span
-- import Language.Granule.Syntax.Type
-- import Language.Granule.Syntax.Identifiers
-- import Language.Granule.Checker.Checker(checkDataCons,checkTyCon)
-- import Language.Granule.Checker.SubstitutionContexts
-- import qualified Language.Granule.Checker.Primitives as Primitives
-- import Language.Granule.Checker.Monad(initState,runAll)
import Language.Granule.Utils

-- import Control.Monad.State.Strict

-- To run just these tests do:
--  stack test granule-frontend --test-arguments "-m "Synth""

spec :: Test.Spec
spec = let ?globals = mempty :: Globals in do
  checkCasePatterns

checkCasePatterns :: Test.Spec
checkCasePatterns = do
  describe "Simple constructor test" $ do
    it "Simple case" $ do
      True `shouldBe` True