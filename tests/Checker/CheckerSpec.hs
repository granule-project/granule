{-# LANGUAGE PartialTypeSignatures #-}

module Checker.CheckerSpec where

import Control.Exception (SomeException, try)
import Control.Monad (forM_)

import System.FilePath.Find
import Test.Hspec

import Checker.Checker
import Syntax.Parser

pathToExamples :: FilePath
pathToExamples = "examples"

pathToNonExamples :: FilePath
pathToNonExamples = "examples/illtyped"

 -- files in these directories don't get checked
exclude1 :: FilePath
exclude1 = "broken"

exclude2 :: FilePath
exclude2 = "illtyped"

fileExtension :: String
fileExtension = ".gr"

spec :: Spec
spec = do
    srcFiles <- runIO exampleFiles
    forM_ srcFiles $ \file ->
      describe file $ it "typechecks" $ do
        parsed <- try $ readFile file >>= parseDefs :: IO (Either SomeException _)
        case parsed of
          Left ex -> expectationFailure (show ex) -- parse error
          Right (ast, nameMap) -> do
            result <- try (check ast False nameMap) :: IO (Either SomeException _)
            case result of
                Left ex -> expectationFailure (show ex) -- an exception was thrown
                Right checked -> checked `shouldBe` Right True

    srcFiles' <- runIO illTypedFiles
    forM_ srcFiles' $ \file ->
      describe file $ it "does not typecheck" $ do
        parsed <- try $ readFile file >>= parseDefs :: IO (Either SomeException _)
        case parsed of
          Left ex -> expectationFailure (show ex) -- parse error
          Right (ast, nameMap) -> do
            result <- try (check ast False nameMap) :: IO (Either SomeException _)
            case result of
                Left ex -> expectationFailure (show ex) -- an exception was thrown
                Right checked -> checked `shouldBe` (Left "")

  where
    exampleFiles =
      find (fileName /=? exclude1 &&? fileName /=? exclude2) (extension ==? fileExtension) pathToExamples

    illTypedFiles =
      find always (extension ==? fileExtension) pathToNonExamples