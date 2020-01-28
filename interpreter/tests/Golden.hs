import Control.Exception (catch, throwIO)
import Control.Monad (unless)
import Data.Algorithm.Diff (getGroupedDiff)
import Data.Algorithm.DiffOutput (ppDiff)
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden (findByExtension, goldenVsFile)
import Test.Tasty.Golden.Advanced (goldenTest)
import System.Directory (renameFile, setCurrentDirectory)
import System.Exit (ExitCode)
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
  rewrite <- goldenTestsRewrite

  catch
    (defaultMain $ testGroup "Golden tests" [negative, positive, rewrite])
    (\(e :: ExitCode) -> do
      -- Move all of the backup files back to their original place.
      backupFiles <- findByExtension [".bak"]  "frontend/tests/cases/rewrite"
      print backupFiles
      _ <- mapM_ (\backup -> renameFile backup (dropExtension backup)) backupFiles
      throwIO e
    )

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

goldenTestsRewrite :: IO TestTree
goldenTestsRewrite = do
  let dir = "frontend/tests/cases/rewrite"

  -- get example files, but discard the excluded ones
  files <- findByExtension granuleFileExtensions dir

  -- ensure we don't have spurious output files without associated tests
  outfiles <- findByExtension [".output"] dir
  failOnOrphanOutfiles files outfiles

  return $ testGroup
    "Golden rewrite examples"
    (map grGolden' files)

  where
    grGolden' :: FilePath -> TestTree
    grGolden' file =
      goldenVsFile file file (file <> ".output") (runGr file)

    runGr :: FilePath -> IO ()
    runGr fp = do
      src <- readFile fp
      let ?globals = goldenGlobals { globalsSourceFilePath = Just fp, globalsRewriteHoles = Just True }
      _ <- Interpreter.run (mempty { Interpreter.grKeepBackup = Just True }) src
      return ()

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
        [ "Contents of " <> outfile <> " (<) and actual output (>) differ:"
        , ppDiff $ getGroupedDiff (lines exp) (lines act)
        ]

    runGr :: FilePath -> IO (Either InterpreterError InterpreterResult)
    runGr fp = do
      src <- readFile fp
      let ?globals = goldenGlobals { globalsSourceFilePath = Just fp }
      Interpreter.run mempty src

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