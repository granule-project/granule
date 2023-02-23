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

    -- Either constructor
    let eitherCon = TyCon $ mkId "Either"
    let either =
          Forall ns [(mkId "a", Type 0), (mkId "b", Type 0)] []
                  (FunTy Nothing Nothing (TyVar $ mkId "a") (TyApp (TyApp eitherCon (TyVar $ mkId "a")) (TyVar $ mkId "b")))

    it "Polymorphic test: `Either a b` vs `Either () ()` - success" $ do
      status <- testCheckConstructor $ checkConstructor False either (TyApp (TyApp eitherCon unitCon) unitCon) []
      status `shouldBe` [Just True]

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
    -- Representation of
    -- data Simple a = Simple a
    -- data Maybe a = Nothing | Just a
    let extras =
          [DataDecl {dataDeclSpan = Span {startPos = (1,1), endPos = (1,17), filename = "simple.gr"}
                    , dataDeclId = (Id "Simple" "Simple")
                    , dataDeclTyVarCtxt = [((Id "a" "a"),Type 0)]
                    , dataDeclKindAnn = Nothing
                    , dataDeclDataConstrs = [DataConstrNonIndexed {dataConstrSpan = Span {startPos = (1,17), endPos = (1,17), filename = "simple.gr"}
                                            , dataConstrId = (Id "Simple" "Simple")
                                            , dataConstrParams = [TyVar (Id "a" "a")]}]}
         ,DataDecl {dataDeclSpan = Span {startPos = (2,1), endPos = (2,28), filename = "simple.gr"}
                    , dataDeclId = (Id "Either" "Either")
                    , dataDeclTyVarCtxt = [((Id "a" "a"),Type 0),((Id "b" "b"),Type 0)]
                    , dataDeclKindAnn = Nothing
                    , dataDeclDataConstrs = [DataConstrNonIndexed {dataConstrSpan = Span {startPos = (2,19), endPos = (2,19), filename = "simple.gr"}
                                                                  , dataConstrId = (Id "Left" "Left")
                                                                  , dataConstrParams = [TyVar (Id "a" "a")]}
                                            ,DataConstrNonIndexed {dataConstrSpan = Span {startPos = (2,28), endPos = (2,28), filename = "simple.gr"}
                                                                  , dataConstrId = (Id "Right" "Right")
                                                                  , dataConstrParams = [TyVar (Id "b" "b")]}]}
         ]
    -- Load in the primitive data constructors first before running the computation synthComputation
    let synthComputation' =
             (conv (runAll checkTyCon (extras ++ Primitives.dataTypes)))
          >> (conv (runAll checkDataCons (extras ++ Primitives.dataTypes)))
          >> synthComputation
    (outputs, dat) <- runStateT (runSynthesiser 1 synthComputation' initState) mempty
    mapM (convertError . fst) outputs
  where
    convertError (Right a) = return $ Just a
    convertError (Left err) = do
      -- Print error message if something went badly wrong
      putStrLn $ show err
      return $ Nothing