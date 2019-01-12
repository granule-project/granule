{-# LANGUAGE ImplicitParams #-}
module Language.Granule.Codegen.NormalisedDefSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test
import Test.QuickCheck
import Language.Granule.Codegen.NormalisedDef
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type hiding (var)
import Language.Granule.Utils
import Debug.Trace

import Language.Granule.Codegen.BuildAST

spec :: Test.Spec
spec = do
  describe "normalising definitions" $ do
    let ?globals = defaultGlobals
    let x = (var "x" int)
    let y = (var "y" int)
    it "curries multi-arg definitions" $ do
        let curried = (normaliseDefinition $
                           def "add" [(arg "x" int), (arg "y" int)]
                               ((val x) `plus` (val y))
                               (tts $ int .-> int .-> int))
        let expected = Left $
                           defun "add" (arg "x" int)
                               (lambdaexp (arg "y" int) (int .-> int)
                                    ((val x) `plus` (val y)))
                               (tts $ int .-> int .-> int)
        curried `shouldBe` expected
    it "hoists multi-argument lambda" $ do
        let hoisted = (normaliseDefinition $
                           def "add" []
                               (lambdaexp (arg "x" int) (int .-> int .-> int)
                                    (lambdaexp (arg "y" int) (int .-> int)
                                        ((val x) `plus` (val y))))
                               (tts $ int .-> int .-> int))
        let expected = Left $
                           defun "add" (arg "x" int)
                              (lambdaexp (arg "y" int) (int .-> int)
                                   ((val x) `plus` (val y)))
                              (tts $ int .-> int .-> int)
        hoisted `shouldBe` expected
    it "desugars multple-arg, multi-equations as case" $ do
        let hoisted = (normaliseDefinition $
                          casedef "xor"
                              [([pint 0, pint 0],           (val (lit 1))),
                               ([pint 1, pint 1],           (val (lit 1))),
                               ([arg "x" int, arg "y" int], (val (lit 0)))]
                              (tts $ int .-> int .-> int))
        let expected = Left $
                           defun "xor" (arg "x" int)
                              (lambdaexp (arg "y" int) (int .-> int)
                                   (caseexpr (val (typedPair (var "x" int) (var "y" int)))
                                       [(ppair (pint 0) (pint 0),
                                            (val (lit 1))),
                                        (ppair (pint 1) (pint 1),
                                            (val (lit 1))),
                                        (ppair (arg "x" int) (arg "y" int),
                                            (val (lit 0)))]))
                              (tts $ int .-> int .-> int)
        hoisted `shouldBe` expected
