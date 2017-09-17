{-# LANGUAGE DoAndIfThenElse #-}

module Checker.CheckerSpec where

import Control.Monad (forM, forM_)
import Data.List ((\\), isSuffixOf)
import System.Directory (doesDirectoryExist, listDirectory, makeAbsolute, withCurrentDirectory)
import System.FilePath (splitDirectories)

import Test.Hspec

import Checker.Checker
import Syntax.Parser


pathToExamples :: FilePath
pathToExamples = "examples"

brokenExamples :: FilePath -- these don't get run
brokenExamples = "broken"

fileExtension :: String
fileExtension = ".gr"

spec :: Spec
spec = do
  exFiles <- runIO $ exampleFiles pathToExamples
  forM_ exFiles $ \file -> do
    src <- runIO $ readFile file
    let (ast, nameMap) = parseDefs src
    checked <- runIO $ check ast False nameMap
    describe (short file) $
      it "typechecks" $
        checked `shouldBe` Right True
  where
    short = last . splitDirectories -- remove everything but the filename

exampleFiles :: FilePath -> IO [FilePath]
exampleFiles path = do
  files <- listDirectory path
  files' <- withCurrentDirectory path $ forM files $ \f -> do
    f' <- makeAbsolute f
    isDir <- doesDirectoryExist f'
    if isDir && not (brokenExamples `isSuffixOf` f') then exampleFiles f'
    else return [f' | fileExtension `isSuffixOf` f']
  return $ concat files'
