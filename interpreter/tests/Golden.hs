import Control.Monad (unless)
import Data.Algorithm.Diff (getGroupedDiff)
import Data.Algorithm.DiffOutput (ppDiff)
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden (findByExtension)
import Test.Tasty.Golden.Advanced (goldenTest)
import System.Directory (setCurrentDirectory)
import System.FilePath (dropExtension)
import qualified System.IO.Strict as Strict (readFile)

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
  files <- findByExtension granuleFileExtensions "frontend/tests/cases/negative"

  -- ensure we don't have spurious output files without associated tests
  outfiles <- findByExtension [".output"] "frontend/tests/cases/negative"
  failOnOrphanOutfiles files outfiles

  return $ testGroup
    "Golden examples, StdLib and positive regressions"
    (map (grGolden formatResult) files)

  where
    formatResult :: Either InterpreterError InterpreterResult -> String
    formatResult = let ?globals = goldenGlobals in \case
        Left err -> formatError err
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
  let outfiles = exampleOutfiles <> positiveOutfiles
  failOnOrphanOutfiles files outfiles

  return $ testGroup
    "Golden examples, StdLib and positive regressions"
    (map (grGolden formatResult) files)

  where
    formatResult :: Either InterpreterError InterpreterResult -> String
    formatResult = let ?globals = goldenGlobals in \case
        Right (InterpreterResult val) -> pretty val
        Left err -> error $ formatError err
        Right NoEval -> mempty

grGolden
  :: (Either InterpreterError InterpreterResult -> String)
  -> FilePath
  -> TestTree
grGolden formatResult file = goldenTest
    file
    (Strict.readFile outfile)
    (formatResult <$> runGr file)
    checkDifference
    (\actual -> unless (null actual) (writeFile outfile actual))
  where
    outfile = file <> ".output"
    checkDifference :: String -> String -> IO (Maybe String)
    checkDifference exp act = if exp == act
      then return Nothing
      else return . Just $ unlines
        [ "Expected (<) and actual (>) output differ:"
        , ppDiff $ getGroupedDiff (lines exp) (lines act)
        ]

    runGr :: FilePath -> IO (Either InterpreterError InterpreterResult)
    runGr fp = do
      src <- readFile fp
      let ?globals = goldenGlobals
      Interpreter.run src

failOnOrphanOutfiles :: [FilePath] -> [FilePath] -> IO ()
failOnOrphanOutfiles files outfiles
  = case filter (\outfile -> dropExtension outfile `notElem` files) outfiles of
    [] -> return ()
    orphans -> error . red $ "Orphan output files:\n" <> unlines orphans
  where
    red x = "\ESC[31;1m" <> x <> "\ESC[0m"

granuleFileExtensions :: [String]
granuleFileExtensions = [".gr", ".gr.md"]

goldenGlobals :: Globals
goldenGlobals = mempty
  { globalsNoColors = Just True
  , globalsSuppressInfos = Just True
  , globalsTesting = Just True
  }

{-
-- This was used to clean up after running tests, previously. Keeping it around
-- here in case we need something like this in future. @buggymcbugfix

-- | Run tests and remove all empty outfiles
runTestsAndCleanUp :: TestTree -> IO ()
runTestsAndCleanUp tests = do
  defaultMain tests `catch` (\(e :: SomeException) -> do
    outfiles <- findByExtension [".output"] "."
    forM_ outfiles $ \outfile -> do
      contents <- readFile outfile
      when (null contents) (removeFile outfile)
    throwIO e)

-}