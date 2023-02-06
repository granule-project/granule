import Control.Exception (catch, throwIO)
import Control.Monad (unless)
import Data.Algorithm.Diff (getGroupedDiff)
import Data.Algorithm.DiffOutput (ppDiff)
import Data.List (sort, isInfixOf)
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden (goldenVsFile)
import qualified Test.Tasty.Golden as G
import Test.Tasty.Golden.Advanced (goldenTest)
import System.Directory (renameFile, setCurrentDirectory)
import System.Exit (ExitCode)
import System.FilePath (dropExtension, pathSeparator)
import qualified System.IO.Strict as Strict (readFile)
import System.Environment

import Language.Granule.Interpreter (InterpreterResult(..), InterpreterError(..))
import qualified Language.Granule.Interpreter as Interpreter
import Language.Granule.Syntax.Pretty (pretty)
import Language.Granule.Utils (Globals (..), formatError)

data Config = IncludeAll Config | Include String Config | Exclude String Config | Nil
  deriving Show

{-
-- e.g., aux "-p simple -p polymorphism -e simple"
--    == IncludeAll (Include "simple" (Include "polymorphism" (Exclude "simple" Nil)))
parseArgsToConfig :: [String] -> Either String Config
-- Otherwise we need to parse the inclusions/exclusions
parseArgsToConfig config = (postProcess False Nil) <$> (aux config)
  where
    -- The list of arguments has includes therefore we will start with no files and add
    postProcess True  res Nil = res
    -- The list of arguments has no includes, therefore include all
    postProcess False res Nil = IncludeAll res
    -- Induct
    postProcess hasInclude res (Include p as) = postProcess True (Include p res) as
    postProcess hasInclude res (Exclude p as) = postProcess hasInclude (Exclude p res) as
    postProcess hasInclude res (IncludeAll c) = postProcess hasInclude (IncludeAll res) c

    -- Any argument starting with `--` is not one we are recognising here
    aux ("--all":zs)     = aux zs >>= return . IncludeAll
    aux (('-':'-':_):zs) = aux zs
    aux ("-a":zs) =
      (aux zs) >>= (return . IncludeAll)
    aux (('-':mode):pattern:zs) =
      case mode of
        "p" -> (aux zs) >>= (return . Include pattern)
        "e" -> (aux zs) >>= (return . Exclude pattern)
        _   -> Left $ "Unknown mode: " <> mode
    aux (_:xs) = aux xs
    aux []     = return Nil
-}

main :: IO ()
main = do
  -- Get patterns from test arguments
  -- e.g., stack test --ta '-p positive'
  args <- getArgs
  let configE = Right (IncludeAll Nil) -- parseArgsToConfig args
  case configE of
    Left error -> do
      putStrLn $ "Error in test arguments: " <> error
    Right config -> do
      -- go into project root
      setCurrentDirectory "../"
      negative  <- goldenTestsNegative  config
      positive  <- goldenTestsPositive  config 
      rewrite   <- goldenTestsRewrite   config
      synthesis <- goldenTestsSynthesis config

      catch
        (defaultMain $ testGroup "Golden tests" [negative, positive, rewrite, synthesis])
        (\(e :: ExitCode) -> do
          -- Move all of the backup files back to their original place.
          backupFiles <- findByExtension config [".bak"]  "frontend/tests/cases/rewrite"
          _ <- mapM_ (\backup -> renameFile backup (dropExtension backup)) backupFiles
          -- and for synthesis
          backupFiles <- findByExtension config [".bak"]  "frontend/tests/cases/synthesis"
          _ <- mapM_ (\backup -> renameFile backup (dropExtension backup)) backupFiles
          throwIO e
        )

-- Applies a configuration to list of filepaths
applyConfig :: Config -> [FilePath] -> [FilePath]
applyConfig cfgs files = aux cfgs []
  where
    aux (IncludeAll cfg) _soFar =
      aux cfg files

    -- Add from the files list those from a directory matching this pattern
    aux (Include pat cfg) soFar =
      aux cfg (soFar ++ filter (\file -> (pat ++ [pathSeparator]) `isInfixOf` file) files)

    -- Remove from the soFar list those from a directory matching this pattern
    aux (Exclude pat cfg) soFar =
      aux cfg (filter (\file -> not $ (pat ++ [pathSeparator]) `isInfixOf` file) soFar)

    aux Nil soFar = soFar


findByExtension :: Config -> [FilePath] -> FilePath -> IO [FilePath]
findByExtension config exs path = G.findByExtension exs path >>= (return . sort . applyConfig config)

goldenTestsNegative :: Config -> IO TestTree
goldenTestsNegative config = do
  -- get example files, but discard the excluded ones
  files <- findByExtension config granuleFileExtensions "frontend/tests/cases/negative"

  -- ensure we don't have spurious output files without associated tests
  outfiles <- findByExtension config [".output"] "frontend/tests/cases/negative"
  failOnOrphanOutfiles files outfiles

  return $ testGroup
    "Golden examples, StdLib and positive regressions"
    (map (grGolden formatResult) files)

  where
    formatResult :: Either InterpreterError InterpreterResult -> String
    formatResult = let ?globals = goldenGlobals in \case
        Left err -> formatError err
        Right x -> error $ "Negative test passed!\n" <> show x


goldenTestsPositive :: Config -> IO TestTree
goldenTestsPositive config = do
  -- get example files, but discard the excluded ones
  exampleFiles  <- findByExtension config granuleFileExtensions "examples"
  stdLibFiles   <- findByExtension config granuleFileExtensions "StdLib"
  positiveFiles <- findByExtension config granuleFileExtensions "frontend/tests/cases/positive"
  let files = exampleFiles <> stdLibFiles <> positiveFiles

  -- ensure we don't have spurious output files without associated tests
  exampleOutfiles  <- findByExtension config [".output"] "examples"
  positiveOutfiles <- findByExtension config [".output"] "frontend/tests/cases/positive"
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

goldenTestsRewrite :: Config -> IO TestTree
goldenTestsRewrite config = do
  let dir = "frontend/tests/cases/rewrite"

  -- get example files, but discard the excluded ones
  files <- findByExtension config granuleFileExtensions dir

  -- ensure we don't have spurious output files without associated tests
  outfiles <- findByExtension config [".output"] dir
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
      let ?globals = goldenGlobals {
        globalsSourceFilePath = Just fp,
        globalsRewriteHoles = Just True,
        globalsIncludePath = Just "StdLib" }
      _ <- Interpreter.run (mempty { Interpreter.grKeepBackup = Just True }) src
      return ()

goldenTestsSynthesis :: Config -> IO TestTree
goldenTestsSynthesis config = do
  let dir = "frontend/tests/cases/synthesis"

  -- get example files, but discard the excluded ones
  files <- findByExtension config granuleFileExtensions dir

  -- ensure we don't have spurious output files without associated tests
  outfiles <- findByExtension config [".output"] dir
  failOnOrphanOutfiles files outfiles

  -- subtractive synthesis check
  let hdir = "frontend/tests/cases/synthesis/hilbert"
  hfiles <- findByExtension config granuleFileExtensions hdir

  return $ testGroup
    "Golden synthesis examples"
    [testGroup 
       "Main: Additive" (map (grGolden' mainGlobals) files)
    -- Do extra tests, running additive pruning and subtractive on the hilbert benchmarks
   , testGroup
       "Additive(pruning)" (map (grGolden' subtractiveGlobals) hfiles)
   , testGroup
       "Subtractive" (map (grGolden' additivePruningGlobals) hfiles)]

  where
    mainGlobals :: FilePath -> Globals
    mainGlobals fp = goldenGlobals {
        globalsSourceFilePath = Just fp,
        globalsSynthesise = Just True,
        globalsRewriteHoles = Just True,
        globalsIncludePath = Just "StdLib" }

    subtractiveGlobals :: FilePath -> Globals
    subtractiveGlobals fp = (mainGlobals fp) { globalsSubtractiveSynthesis = Just True }

    additivePruningGlobals :: FilePath -> Globals
    additivePruningGlobals fp = (mainGlobals fp) { globalsAlternateSynthesisMode = Just True }

    grGolden' :: (FilePath -> Globals) -> FilePath -> TestTree
    grGolden' gl file =
      goldenVsFile file file (file <> ".output") (runGr gl file)

    runGr :: (FilePath -> Globals) -> FilePath -> IO ()
    runGr gl fp = do
      src <- readFile fp
      let ?globals = gl fp
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