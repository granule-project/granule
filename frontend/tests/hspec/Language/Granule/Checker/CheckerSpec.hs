{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.CheckerSpec where

import Control.Exception (SomeException, try)
import Control.Monad (forM_, liftM2)
import Data.Either (isLeft, isRight, fromRight)

import System.FilePath.Find
import Test.Hspec

import Language.Granule.Checker.Checker
import Language.Granule.Checker.Constraints
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Monad
import Language.Granule.Syntax.Parser
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Annotated
import Language.Granule.Utils
import Language.Granule.TestUtils
import System.Directory (setCurrentDirectory)

pathToExamples :: FilePath
pathToExamples = "examples"

pathToRegressionTests :: FilePath
pathToRegressionTests = "frontend/tests/cases/positive"

pathToIlltyped :: FilePath
pathToIlltyped = "frontend/tests/cases/negative"

 -- files in these directories don't get checked
exclude :: FilePath
exclude = ""

fileExtensions :: [String]
fileExtensions = [".gr"] -- todo: .md

spec :: Spec
spec = do
    runIO $ setCurrentDirectory "../"
    -- Working directory must be root of project for StdLib
    -- imports to work

    -- Integration tests based on the fixtures
    let ?globals = defaultGlobals { suppressInfos = True }
    srcFiles <- runIO exampleFiles
    forM_ srcFiles $ \file ->
      describe file $ it "should typecheck" $ do
        let ?globals = ?globals { sourceFilePath = file }
        parsed <- try $ readFile file >>= parseAndDoImportsAndFreshenDefs
        case parsed of
          Left (ex :: SomeException) -> expectationFailure (show ex) -- parse error
          Right ast -> do
            result <- try (check ast)
            case result of
                Left (ex :: SomeException) -> expectationFailure (show ex) -- an exception was thrown
                Right checked -> checked `shouldSatisfy` isRight
    -- Negative tests: things which should fail to check
    srcFiles <- runIO illTypedFiles
    forM_ srcFiles $ \file ->
      describe file $ it "should not typecheck" $ do
        let ?globals = ?globals { sourceFilePath = file, suppressErrors = True }
        parsed <- try $ readFile file >>= parseAndDoImportsAndFreshenDefs
        case parsed of
          Left (ex :: SomeException) -> expectationFailure (show ex) -- parse error
          Right ast -> do
            result <- try (check ast)
            case result of
                Left (ex :: SomeException) -> expectationFailure (show ex) -- an exception was thrown
                Right checked -> checked `shouldSatisfy` isLeft

    let tyVarK = TyVar $ mkId "k"
    let varA = mkId "a"

    -- Unit tests
    describe "joinCtxts" $ do
     it "join ctxts with discharged assumption in both" $ do
       (c, pred) <- runCtxts joinCtxts
              [(varA, Discharged tyVarK (CSig (CNat 5) natInterval))]
              [(varA, Discharged tyVarK (cNatOrdered 10))]
       c `shouldBe` [(varA, Discharged tyVarK (CVar (mkId "a")))]
       pred `shouldBe`
         [Conj [Con (ApproximatedBy nullSpan (cNatOrdered 10) (CVar (mkId "a")) natInterval)
              , Con (ApproximatedBy nullSpan (cNatOrdered 5) (CVar (mkId "a")) natInterval)]]

     it "join ctxts with discharged assumption in one" $ do
       (c, pred) <- runCtxts joinCtxts
              [(varA, Discharged (tyVarK) (cNatOrdered 5))]
              []
       c `shouldBe` [(varA, Discharged (tyVarK) (CVar (mkId "a")))]
       pred `shouldBe`
         [Conj [Con (ApproximatedBy nullSpan (CZero natInterval) (CVar (mkId "a")) natInterval)
               ,Con (ApproximatedBy nullSpan (cNatOrdered 5) (CVar (mkId "a")) natInterval)]]


    describe "intersectCtxtsWithWeaken" $ do
      it "contexts with matching discharged variables" $ do
         (c, _) <- (runCtxts intersectCtxtsWithWeaken)
                 [(varA, Discharged (tyVarK) (cNatOrdered 5))]
                 [(varA, Discharged (tyVarK) (cNatOrdered 10))]
         c `shouldBe`
                 [(varA, Discharged (tyVarK) (cNatOrdered 5))]

      it "contexts with matching discharged variables" $ do
         (c, _) <- (runCtxts intersectCtxtsWithWeaken)
                 [(varA, Discharged (tyVarK) (cNatOrdered 10))]
                 [(varA, Discharged (tyVarK) (cNatOrdered 5))]
         c `shouldBe`
                 [(varA, Discharged (tyVarK) (cNatOrdered 10))]

      it "contexts with matching discharged variables" $ do
         (c, preds) <- (runCtxts intersectCtxtsWithWeaken)
                 [(varA, Discharged (tyVarK) (cNatOrdered 5))]
                 []
         c `shouldBe`
                 [(varA, Discharged (tyVarK) (cNatOrdered 5))]

      it "contexts with matching discharged variables (symm)" $ do
         (c, _) <- (runCtxts intersectCtxtsWithWeaken)
                 []
                 [(varA, Discharged (tyVarK) (cNatOrdered 5))]
         c `shouldBe`
                 [(varA, Discharged (tyVarK) (CZero
                     (TyApp (TyCon $ mkId "Interval") (TyCon $ mkId "Nat"))))]


    describe "elaborator tests" $
      it "simple elaborator tests" $ do
        -- Simple definitions
        -- \x -> x + 1
        (AST _ (def1:_)) <- parseAndDoImportsAndFreshenDefs "foo : Int -> Int\nfoo x = x + 1"
        (Right defElab, _) <- runChecker initState (checkDef [] def1)
        annotation (extractMainExpr defElab) `shouldBe` (TyCon $ mkId "Int")


extractMainExpr (Def _ _ [(Equation _ _ _ e)] _) = e

runCtxts
  :: (?globals::Globals)
  => (Span -> a -> a -> Checker a)
  -> a
  -> a
  -> IO (a, [Pred])
runCtxts f a b = do
  (Right res, state) <- runChecker initState (f nullSpan a b)
  pure (res, predicateStack state)

exampleFiles = foldr1 (liftM2 (<>)) $ do
    fileExtension <- fileExtensions
    id [ find (fileName /=? exclude) (extension ==? fileExtension) pathToExamples
       , find always (extension ==? fileExtension) (includePath defaultGlobals)
       , find always (extension ==? fileExtension) pathToRegressionTests
       ] -- `id` in order to indent list, otherwise it doesn't parse in `do` notation

cNatOrdered x = CSig (CNat x) natInterval
natInterval = TyApp (TyCon $ mkId "Interval") (TyCon $ mkId "Nat")

illTypedFiles = foldr1 (liftM2 (<>)) $ do
      fileExtension <- fileExtensions
      [ find always (extension ==? fileExtension) pathToIlltyped ]
