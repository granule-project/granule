module Language.Granule.Synthesis.CommonSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test

import Language.Granule.Synthesis.Common
import Language.Granule.Synthesis.Monad
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
import Language.Granule.Checker.Checker(checkDataCons,checkTyCon)
import Language.Granule.Checker.SubstitutionContexts
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Checker.Monad(initState,runAll)
import Language.Granule.Utils

import Control.Monad.State.Strict

-- To run just these tests do:
--  stack test granule-frontend --test-arguments "-m "Common""

spec :: Test.Spec
spec = let ?globals = mempty :: Globals in do


  describe "Tests on checkConstructor" $ do
    let unitCon = TyCon (mkId "()")
    it "Monomorphic test: unit" $ do
      -- A unit constructor matches a unit goal
      status <- testCheckConstructor
                   $ checkConstructor False (Forall ns [] [] unitCon) unitCon []
      status `shouldBe` [Just True]

    -- A simple constructor with a polymorphic type
    -- MkSimple :: Simple a
    let simpleCon = TyCon $ mkId "Simple"
    let simple = Forall ns [(mkId "a", Type 0)] [] (TyApp simpleCon (TyVar $ mkId "a"))

    it "Polymorphic test: `Simple a` vs () - fail" $ do
      status <- testCheckConstructor $ checkConstructor False simple unitCon []
      status `shouldBe` []
    it "Polymorphic test: `Simple a` vs Simple () - success" $ do
      status <- testCheckConstructor $ checkConstructor False simple (TyApp simpleCon unitCon) []
      status `shouldBe` [Just True]

    -- Maybe-style constructor
    -- let maybeCon = TyCon $ mkId "Maybe"
    -- let maybe = Forall ns [(mkId "a", Type 0)] [] ()
    return ()


-- Helper for running checkConstructor specifically
testCheckConstructor :: (?globals :: Globals) => Synthesiser (Bool, Type, [(Type, Maybe Coeffect)], Substitution, Substitution)
                                              -> IO [Maybe Bool]
testCheckConstructor m = do
  constr <- testSynthesiser m
  let status = map (fmap (\(status, _, _, _, _) -> status)) constr
  return status

-- Helper for running the synthesiser
testSynthesiser :: (?globals :: Globals) => Synthesiser a -> IO [Maybe a]
testSynthesiser synthComputation = do
    -- Representation of a simple ty con
    let simpleTyCon =
          DataDecl {dataDeclSpan = Span {startPos = (1,1), endPos = (1,17), filename = "simple.gr"}
                    , dataDeclId = (Id "Simple" "Simple")
                    , dataDeclTyVarCtxt = [((Id "a" "a"),Type 0)]
                    , dataDeclKindAnn = Nothing
                    , dataDeclDataConstrs = [DataConstrNonIndexed {dataConstrSpan = Span {startPos = (1,17), endPos = (1,17), filename = "simple.gr"}
                    , dataConstrId = (Id "Simple" "Simple")
                    , dataConstrParams = [TyVar (Id "a" "a")]}]}
    -- Load in the primitive data constructors first before running the computation synthComputation
    let synthComputation' =
             (conv (runAll checkTyCon (simpleTyCon : Primitives.dataTypes)))
          >> (conv (runAll checkDataCons (simpleTyCon : Primitives.dataTypes)))
          >> synthComputation
    (outputs, dat) <- runStateT (runSynthesiser 1 synthComputation' initState) mempty
    mapM (convertError . fst) outputs
  where
    convertError (Right a) = return $ Just a
    convertError (Left err) = do
      -- Print error message if something went badly wrong
      putStrLn $ show err
      return $ Nothing