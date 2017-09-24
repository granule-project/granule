{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
    forM_ srcFiles $ \file -> do
      parsed <- runIO (try $ readFile file >>= parseDefs :: IO (Either SomeException _))
      case parsed of
        Left ex -> describe file $ it "typechecks" $ expectationFailure (show ex)
        Right (ast, nameMap) -> do
          result <- runIO (try (check ast False nameMap) :: IO (Either SomeException _))
          describe file $ it "typechecks" $
            case result of
              Right checked -> checked `shouldBe` Right True -- no exception thrown
              Left ex -> expectationFailure (show ex) -- an exception was thrown
  where
    exampleFiles =
      find (fileName /=? exclude) (extension ==? fileExtension) pathToExamples
