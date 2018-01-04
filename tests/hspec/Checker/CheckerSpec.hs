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
import Utils


pathToExamples :: FilePath
pathToExamples = "examples/good"

pathToGranuleBase :: FilePath
pathToGranuleBase = "StdLib"

pathToIlltyped :: FilePath
pathToIlltyped = "examples/illtyped"

 -- files in these directories don't get checked
exclude :: FilePath
exclude = ""

fileExtension :: String
fileExtension = ".gr"

tyvark = TyVar $ mkId "k"
varA = mkId "a"

spec :: Spec
spec = do
    -- Integration tests based on the fixtures
    let ?globals = defaultGlobals { suppressInfos = True, suppressErrors = True }
    srcFiles <- runIO exampleFiles
    forM_ srcFiles $ \file ->
      describe file $ it "typechecks" $ do
        let ?globals = ?globals { sourceFilePath = file }
        parsed <- try $ readFile file >>= parseDefs :: IO (Either SomeException _)
        case parsed of
          Left ex -> expectationFailure (show ex) -- parse error
          Right (ast, maxFreshId) -> do
            result <- try (check ast maxFreshId) :: IO (Either SomeException _)
            case result of
                Left ex -> expectationFailure (show ex) -- an exception was thrown
                Right checked -> checked `shouldBe` Ok
    -- Negative tests: things which should fail to check
    srcFiles <- runIO illTypedFiles
    forM_ srcFiles $ \file ->
      describe file $ it "does not typecheck" $ do
        let ?globals = ?globals { sourceFilePath = file }
        parsed <- try $ readFile file >>= parseDefs :: IO (Either SomeException _)
        case parsed of
          Left ex -> expectationFailure (show ex) -- parse error
          Right (ast, maxFreshId) -> do
            result <- try (check ast maxFreshId) :: IO (Either SomeException _)
            case result of
                Left ex -> expectationFailure (show ex) -- an exception was thrown
                Right checked -> checked `shouldBe` Failed

    -- Unit tests
    describe "joinCtxts" $ do
     it "join ctxts with discharged assumption in both" $ do
       (c, pred) <- runCtxts joinCtxts
              [(varA, Discharged tyvark (CNat Ordered 5))]
              [(varA, Discharged tyvark (CNat Ordered 10))]
       c `shouldBe` [(varA, Discharged tyvark (CVar (mkId "a0")))]
       pred `shouldBe`
         [Conj [Con (Leq nullSpan (CNat Ordered 10) (CVar (mkId "a0")) (CConstr "Nat"))
              , Con (Leq nullSpan (CNat Ordered 5) (CVar (mkId "a0")) (CConstr "Nat"))]]

     it "join ctxts with discharged assumption in one" $ do
       (c, pred) <- runCtxts joinCtxts
              [(varA, Discharged (tyvark) (CNat Ordered 5))]
              []
       c `shouldBe` [(varA, Discharged (tyvark) (CVar (mkId "a0")))]
       pred `shouldBe`
         [Conj [Con (Leq nullSpan (CZero (CConstr "Nat")) (CVar (mkId "a0")) (CConstr "Nat"))
               ,Con (Leq nullSpan (CNat Ordered 5) (CVar (mkId "a0")) (CConstr "Nat"))]]


    describe "intersectCtxtsWithWeaken" $ do
      it "contexts with matching discharged variables" $ do
         (c, _) <- (runCtxts intersectCtxtsWithWeaken)
                 [(varA, Discharged (tyvark) (CNat Ordered 5))]
                 [(varA, Discharged (tyvark) (CNat Ordered 10))]
         c `shouldBe`
                 [(varA, Discharged (tyvark) (CNat Ordered 5))]

      it "contexts with matching discharged variables" $ do
         (c, _) <- (runCtxts intersectCtxtsWithWeaken)
                 [(varA, Discharged (tyvark) (CNat Ordered 10))]
                 [(varA, Discharged (tyvark) (CNat Ordered 5))]
         c `shouldBe`
                 [(varA, Discharged (tyvark) (CNat Ordered 10))]

      it "contexts with matching discharged variables" $ do
         (c, preds) <- (runCtxts intersectCtxtsWithWeaken)
                 [(varA, Discharged (tyvark) (CNat Ordered 5))]
                 []
         c `shouldBe`
                 [(varA, Discharged (tyvark) (CNat Ordered 5))]

      it "contexts with matching discharged variables (symm)" $ do
         (c, _) <- (runCtxts intersectCtxtsWithWeaken)
                 []
                 [(varA, Discharged (tyvark) (CNat Ordered 5))]
         c `shouldBe`
                 [(varA, Discharged (tyvark) (CZero (CConstr "Nat")))]



  where
    runCtxts f a b =
       runChecker initState (runMaybeT (f nullSpan a b))
          >>= (\(x, state) -> return (fromJust x, predicateStack state))
    exampleFiles = liftM2 (++)
      (find (fileName /=? exclude) (extension ==? fileExtension) pathToExamples)
      (find always (extension ==? fileExtension) pathToGranuleBase)

    illTypedFiles =
      find always (extension ==? fileExtension) pathToIlltyped
