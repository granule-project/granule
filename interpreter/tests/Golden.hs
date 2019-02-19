import Control.Monad (forM_, unless)
import Data.List ((\\))
import Data.Maybe (isJust)
import Data.ByteString.Lazy.UTF8 (ByteString, fromString)
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString, findByExtension)
import System.Directory (setCurrentDirectory)
import System.FilePath (dropExtension, takeFileName, replaceExtension)

import Language.Granule.Interpreter (InterpreterResult(..), InterpreterError(..))
import qualified Language.Granule.Interpreter as Interpreter
import Language.Granule.Syntax.Pretty (pretty)
import Language.Granule.Utils (Globals (..), formatError)

main :: IO ()
main = do
  -- go into project root
  setCurrentDirectory "../"
  negative <- goldenTestsNegative
  positive <- goldenTestsPositive
  defaultMain $ testGroup "Golden tests" [negative, positive]

goldenTestsNegative :: IO TestTree
goldenTestsNegative = do
  -- get example files, but discard the excluded ones
  files <- findByExtension [".gr", ".gr.md"] "frontend/tests/cases/negative"

  -- ensure we don't have spurious output files without associated tests
  outfiles <- findByExtension [".output"] "frontend/tests/cases/negative"
  forM_ outfiles $ \outfile ->
    unless (dropExtension outfile `elem` files)
      (error $ "Orphan output file: " <> outfile)

  return $ testGroup "negative test cases"
    [ goldenVsString
        (takeFileName file) -- test name
        (file <> ".output") -- golden file path
        (formatResult . snd <$> runGr file) -- action whose result is tested
    | file <- files
    ]
  where
    formatResult :: Either InterpreterError InterpreterResult -> ByteString
    formatResult = let ?globals = goldenGlobals in \case
        Left err -> fromString $ formatError err
        Right x -> error $ "Negative test passed!\n" <> show x


goldenTestsPositive :: IO TestTree
goldenTestsPositive = do
  -- get example files, but discard the excluded ones
  exampleFiles  <- findByExtension [".gr", ".gr.md"] "examples"
  positiveFiles <- findByExtension [".gr", ".gr.md"] "frontend/tests/cases/positive"
  let files = exampleFiles <> positiveFiles

  -- ensure we don't have spurious output files without associated tests
  exampleOutfiles  <- findByExtension [".output"] "examples"
  positiveOutfiles <- findByExtension [".output"] "frontend/tests/cases/positive"
  forM_ (exampleOutfiles <> positiveOutfiles) $ \outfile ->
    unless (dropExtension outfile `elem` files)
      (error $ "Orphan output file: " <> outfile)

  positiveFiles <- findByExtension [".gr", ".gr.md"] "frontend/tests/cases/positive"

  -- only check outputs for tests that evaluated to something
  results
    <- filter ((\case Right NoEval -> False; _ -> True) . snd)
    <$> mapM runGr files

  return $ testGroup "positive type checking and evaluation cases"
    [ goldenVsString
        (takeFileName file) -- test name
        (file <> ".output") -- golden file path
        (pure $ formatResult result) -- action whose result is tested
    | (file, result) <- results
    ]
  where
    formatResult :: Either InterpreterError InterpreterResult -> ByteString
    formatResult = let ?globals = goldenGlobals in \case
        Right (InterpreterResult val) -> fromString $ pretty val
        Left err -> error $ formatError err
        Right NoEval -> error "I want refinement types"

runGr :: FilePath -> IO ((FilePath, Either InterpreterError InterpreterResult))
runGr fp = do
  -- putStr fp
  src <- readFile fp
  let ?globals = goldenGlobals
  (,) fp <$> Interpreter.run src

goldenGlobals :: Globals
goldenGlobals = mempty
  { globalsNoColors = Just True
  , globalsSuppressInfos = Just True
  , globalsTesting = Just True
  }