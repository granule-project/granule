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

exclude :: FilePath -- files in this directory don't get checked
exclude = "broken"

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
  where
    exampleFiles =
      find (fileName /=? exclude) (extension ==? fileExtension) pathToExamples
