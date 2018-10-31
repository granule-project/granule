{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ImplicitParams #-}

module Checker.CheckerSpec where

import Control.Exception (SomeException, try)
import Control.Monad (forM_, liftM2)
import Data.Maybe (fromJust)

import System.FilePath.Find
import Test.Hspec

import Checker.Checker
import Checker.Constraints
import Checker.Predicates
import Checker.Monad
import Control.Monad.Trans.Maybe
import Syntax.Parser
import Syntax.Expr
import Syntax.Type
import Syntax.Span
import Syntax.Identifiers
import Utils


pathToExamples :: FilePath
pathToExamples = "examples"

pathToGranuleBase :: FilePath
pathToGranuleBase = "StdLib"

pathToRegressionTests :: FilePath
pathToRegressionTests = "tests/regression/good"

pathToIlltyped :: FilePath
pathToIlltyped = "tests/regression/illtyped"

 -- files in these directories don't get checked
exclude :: FilePath
exclude = ""

fileExtension :: String
fileExtension = ".gr"

spec :: Spec
spec = do
    -- Integration tests based on the fixtures
    let ?globals = defaultGlobals { suppressInfos = True }
    srcFiles <- runIO exampleFiles
    forM_ srcFiles $ \file ->
      describe file $ it "typechecks" $ do
        let ?globals = ?globals { sourceFilePath = file }
        parsed <- try $ readFile file >>= parseDefs :: IO (Either SomeException _)
        case parsed of
          Left ex -> expectationFailure (show ex) -- parse error
          Right ast -> do
            result <- try (check ast) :: IO (Either SomeException _)
            case result of
                Left ex -> expectationFailure (show ex) -- an exception was thrown
                Right checked -> checked `shouldBe` Ok
    -- Negative tests: things which should fail to check
    srcFiles <- runIO illTypedFiles
    forM_ srcFiles $ \file ->
      describe file $ it "does not typecheck" $ do
        let ?globals = ?globals { sourceFilePath = file, suppressErrors = True }
        parsed <- try $ readFile file >>= parseDefs :: IO (Either SomeException _)
        case parsed of
          Left ex -> expectationFailure (show ex) -- parse error
          Right ast -> do
            result <- try (check ast) :: IO (Either SomeException _)
            case result of
                Left ex -> expectationFailure (show ex) -- an exception was thrown
                Right checked -> checked `shouldBe` Failed

    -- Unit tests
    describe "joinCtxts" $ do
     it "join ctxts with discharged assumption in both" $ do
       (c, pred) <- runCtxts joinCtxts
              [(varA, Discharged tyVarK (CNat Ordered 5))]
              [(varA, Discharged tyVarK (CNat Ordered 10))]
       c `shouldBe` [(varA, Discharged tyVarK (CVar (mkId "a.0")))]
       pred `shouldBe`
         [Conj [Con (ApproximatedBy nullSpan (CNat Ordered 10) (CVar (mkId "a.0")) (TyCon $ mkId "Nat"))
              , Con (ApproximatedBy nullSpan (CNat Ordered 5) (CVar (mkId "a.0")) (TyCon $ mkId "Nat"))]]

     it "join ctxts with discharged assumption in one" $ do
       (c, pred) <- runCtxts joinCtxts
              [(varA, Discharged (tyVarK) (CNat Ordered 5))]
              []
       c `shouldBe` [(varA, Discharged (tyVarK) (CVar (mkId "a.0")))]
       pred `shouldBe`
         [Conj [Con (ApproximatedBy nullSpan (CZero (TyCon $ mkId "Nat")) (CVar (mkId "a.0")) (TyCon $ mkId "Nat"))
               ,Con (ApproximatedBy nullSpan (CNat Ordered 5) (CVar (mkId "a.0")) (TyCon $ mkId"Nat"))]]


    describe "intersectCtxtsWithWeaken" $ do
      it "contexts with matching discharged variables" $ do
         (c, _) <- (runCtxts intersectCtxtsWithWeaken)
                 [(varA, Discharged (tyVarK) (CNat Ordered 5))]
                 [(varA, Discharged (tyVarK) (CNat Ordered 10))]
         c `shouldBe`
                 [(varA, Discharged (tyVarK) (CNat Ordered 5))]

      it "contexts with matching discharged variables" $ do
         (c, _) <- (runCtxts intersectCtxtsWithWeaken)
                 [(varA, Discharged (tyVarK) (CNat Ordered 10))]
                 [(varA, Discharged (tyVarK) (CNat Ordered 5))]
         c `shouldBe`
                 [(varA, Discharged (tyVarK) (CNat Ordered 10))]

      it "contexts with matching discharged variables" $ do
         (c, preds) <- (runCtxts intersectCtxtsWithWeaken)
                 [(varA, Discharged (tyVarK) (CNat Ordered 5))]
                 []
         c `shouldBe`
                 [(varA, Discharged (tyVarK) (CNat Ordered 5))]

      it "contexts with matching discharged variables (symm)" $ do
         (c, _) <- (runCtxts intersectCtxtsWithWeaken)
                 []
                 [(varA, Discharged (tyVarK) (CNat Ordered 5))]
         c `shouldBe`
                 [(varA, Discharged (tyVarK) (CZero (TyCon $ mkId "Nat")))]



  where
    runCtxts f a b =
       runChecker initState (runMaybeT (f nullSpan a b))
          >>= (\(x, state) -> return (fromJust x, predicateStack state))
    exampleFiles = liftM2 (<>) -- TODO I tried using `liftM concat` but that didn't work
      (liftM2 (<>) (find (fileName /=? exclude) (extension ==? fileExtension) pathToExamples)
      (find always (extension ==? fileExtension) pathToGranuleBase))
      (find always (extension ==? fileExtension) pathToRegressionTests)

    illTypedFiles =
      find always (extension ==? fileExtension) pathToIlltyped
    tyVarK = TyVar $ mkId "k"
    varA = mkId "a"
