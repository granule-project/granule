module Checker.CheckerSpec where

import Control.Monad (forM_)

import System.FilePath.Find
import Test.Hspec

import Checker.Checker
import Syntax.Parser

pathToExamples :: FilePath
pathToExamples = "examples"

exclude :: FilePath -- these don't get run
exclude = "broken"

fileExtension :: String
fileExtension = ".gr"

spec :: Spec
spec = parallel $ do
  exFiles <- runIO exampleFiles
  forM_ exFiles $ \file -> do
    src <- runIO $ readFile file
    let (ast, nameMap) = parseDefs src
    checked <- runIO $ check ast False nameMap
    describe file $
      it "typechecks" $
        checked `shouldBe` Right True
  where
    exampleFiles =
      find (fileName /=? exclude) (extension ==? fileExtension) pathToExamples
