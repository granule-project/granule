{-# LANGUAGE ImplicitParams #-}
module Language.Granule.Codegen.TopsortDefinitionsSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test
import Test.QuickCheck
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type ((.->), Type)
import Language.Granule.Utils

import Language.Granule.Codegen.NormalisedDef
import Language.Granule.Codegen.TopsortDefinitions
import Language.Granule.Codegen.BuildAST

import Debug.Trace

spec :: Test.Spec
spec = do
  describe "topsorting definitions" $ do
    let ?globals = defaultGlobals
    it "identifies trivially recursive values" $ do
        let recursiveValueDef = (defval "x"
                                    ((val (var "x" int)) `plus` (val (var "add" int)))
                                    (tts $ int))
        let expectedResult = RecursiveValues [recursiveValueDef]
        let actualResult = topologicallySortDefinitions (NormalisedAST [] [] [recursiveValueDef]) :: TopsortResult () Type
        actualResult `shouldBe` expectedResult
    it "identifies mutually recursive values" $ do
        let f = defval "f"
                    ((val (var "g" int)) `plus` (val (lit 10)))
                    (tts $ int)
        let g = defval "g"
                    ((val (var "f" int)) `plus` (val (lit 10)))
                    (tts $ int)
        let h = defval "h"
                    ((val (lit 11)) `plus` (val (lit 10)))
                    (tts $ int)
        let expectedResult = InitializationCycle [] [f, g]
        let actualResult = topologicallySortDefinitions (NormalisedAST [] [] [f, g, h]) :: TopsortResult () Type
        actualResult `shouldBe` expectedResult
    it "identifies more complex mutually recursive values" $ do
        let f = defval "f"
                    ((val (var "g" int)) `plus` (val (lit 10)))
                    (tts $ int)
        let g = defval "g"
                    ((val (var "h" int)) `plus` (val (lit 10)))
                    (tts $ int)
        let h = defval "h"
                    ((val (var "f" int)) `plus` (val (lit 10)))
                    (tts $ int)
        let expectedResult = InitializationCycle [] [f, g, h]
        let actualResult = topologicallySortDefinitions (NormalisedAST [] [] [f, g, h]) :: TopsortResult () Type
        actualResult `shouldBe` expectedResult
    it "identified initialization cycle in first class function" $ do
        let f = defun "f" (arg "x" (int .-> int))
                    (val (var "x" (int .-> int)))
                    (tts $ (int .-> int) .-> (int .-> int))
        let y = defval "y"
                    (app
                        (val (var "f" ((int .-> int) .-> (int .-> int))))
                        (lambdaexp (arg "x" int) (int .-> int)
                            (app (val (var "n" (int .-> int)))
                                 (val (var "x" int)))))
                    (tts $ int .-> int)
        let n = defun "n" (arg "g" int)
                    (app (val (var "y" (int .-> int)))
                         (val (var "g" int)))
                    (tts $ int .-> int)
        let main = defval "main"
                       (app (val (var "y" (int .-> int)))
                            (val (lit 10)))
                       (tts $ int)

        let expectedResult = InitializationCycle [n] [y]
        let actualResult = topologicallySortDefinitions (NormalisedAST [] [f, n] [y, main]) :: TopsortResult () Type
        actualResult `shouldBe` expectedResult
    it "accepts trivially valid ast" $ do
        let valid = (NormalisedAST [] [] [defval "f" (val (lit 10)) (tts $ int)])
        let actualResult = topologicallySortDefinitions valid :: TopsortResult () Type
        actualResult `shouldBe` (Ok valid)
    it "sorts valid ast containing values only" $ do
        let f = defval "f"
                    ((val (var "g" int)) `plus` (val (var "h" int)))
                    (tts $ int)
        let g = defval "g"
                    ((val (var "i" int)) `plus` (val (var "j" int)))
                    (tts $ int)
        let h = defval "h" (val (lit 10)) (tts $ int)
        let i = defval "i" (val (lit 11)) (tts $ int)
        let j = defval "j" (val (lit 12)) (tts $ int)

        let unsorted = (NormalisedAST [] [] [f, g, h, i, j])
        let sorted = (NormalisedAST [] [] [i, j, g, h, f])
        let actualResult = topologicallySortDefinitions unsorted :: TopsortResult () Type
        let expectedResult = Ok sorted
        actualResult `shouldBe` expectedResult
