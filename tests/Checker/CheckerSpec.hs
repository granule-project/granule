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
spec = {-parallel $-} do -- no apparent speedup from `parallel` at the moment
    srcFiles <- runIO exampleFiles
    forM_ srcFiles $ \file -> do
      src <- runIO $ readFile file
      let (ast, nameMap) = parseDefs src
      checked <- runIO $ check ast False nameMap
      describe file $
        it "typechecks" $
          checked `shouldBe` Right True
  where
    exampleFiles =
      find (fileName /=? exclude) (extension ==? fileExtension) pathToExamples
