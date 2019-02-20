import Control.Exception
import Control.Monad (forM_, unless, when)
import Data.List ((\\))
import Data.Maybe (isJust)
import Data.ByteString.Lazy.UTF8 (ByteString, fromString)
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString, findByExtension)
import System.Directory (removeFile, setCurrentDirectory)
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
  runTestsAndCleanUp $ testGroup "Golden tests" [negative, positive]

-- | Run tests and remove all empty outfiles
runTestsAndCleanUp :: TestTree -> IO ()
runTestsAndCleanUp tests = do
  defaultMain tests `catch` (\(e :: SomeException) -> do
    outfiles <- findByExtension [".output"] "."
    forM_ outfiles $ \outfile -> do
      contents <- readFile outfile
      when (null contents) (removeFile outfile)
    throwIO e)

goldenTestsNegative :: IO TestTree
goldenTestsNegative = do
  -- get example files, but discard the excluded ones
  files <- findByExtension granuleFileExtensions "frontend/tests/cases/negative"

  -- ensure we don't have spurious output files without associated tests
  outfiles <- findByExtension [".output"] "frontend/tests/cases/negative"
  forM_ outfiles $ \outfile ->
    unless (dropExtension outfile `elem` files)
      (error $ "Orphan output file: " <> outfile)

  return $ testGroup "negative test cases"
    [ goldenVsString
        file -- test name
        (file <> ".output") -- golden file path
        (formatResult <$> runGr file) -- action whose result is tested
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
  exampleFiles  <- findByExtension granuleFileExtensions "examples"
  stdLibFiles   <- findByExtension granuleFileExtensions "StdLib"
  positiveFiles <- findByExtension granuleFileExtensions "frontend/tests/cases/positive"
  let files = exampleFiles <> stdLibFiles <> positiveFiles

  -- ensure we don't have spurious output files without associated tests
  exampleOutfiles  <- findByExtension [".output"] "examples"
  positiveOutfiles <- findByExtension [".output"] "frontend/tests/cases/positive"
  forM_ (exampleOutfiles <> positiveOutfiles) $ \outfile ->
    unless (dropExtension outfile `elem` files)
      (error $ "Orphan output file: " <> outfile)

  return $ testGroup "positive type checking and evaluation cases"
    [ goldenVsString
        file -- test name
        (file <> ".output") -- golden file path
        (formatResult <$> runGr file) -- action whose result is tested
    | file <- files
    ]
  where
    formatResult :: Either InterpreterError InterpreterResult -> ByteString
    formatResult = let ?globals = goldenGlobals in \case
        Right (InterpreterResult val) -> fromString $ pretty val
        Left err -> error $ formatError err
        Right NoEval -> mempty

runGr :: FilePath -> IO (Either InterpreterError InterpreterResult)
runGr fp = do
  src <- readFile fp
  let ?globals = goldenGlobals
  Interpreter.run src

granuleFileExtensions :: [String]
granuleFileExtensions = [".gr", ".gr.md"]

goldenGlobals :: Globals
goldenGlobals = mempty
  { globalsNoColors = Just True
  , globalsSuppressInfos = Just True
  , globalsTesting = Just True
  }