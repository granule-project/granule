module Checker.CheckerSpec where

import Control.Monad (forM_)
import Data.List ((\\), isPrefixOf)
import Debug.Trace (trace)
import System.Directory

import Test.Hspec

import Checker.Checker
import Syntax.Parser


spec :: Spec
spec = do
  exampleFiles <- runIO $ listDirectory dir
  let files = exampleFiles \\ exclude
  forM_ files $ \file -> do
    src <- runIO $ withCurrentDirectory dir $ readFile file
    let (ast, nameMap) = parseDefs src
    checked <- runIO $ check ast False nameMap
    describe file $
      it "typechecks" $
        checked `shouldBe` Right True
  where
    dir = "examples"
    exclude = ["rec.gr","gex0.gr"]
