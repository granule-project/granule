{-                                       ___
                                        /\_ \
       __   _  _    __      ___   __  __\//\ \      __
     / _  \/\`'__\/ __ \  /' _ `\/\ \/\ \ \ \ \   /'__`\
    /\ \_\ \ \ \//\ \_\ \_/\ \/\ \ \ \_\ \ \_\ \_/\  __/
    \ \____ \ \_\\ \__/ \_\ \_\ \_\ \____/ /\____\ \____\
     \/___L\ \/_/ \/__/\/_/\/_/\/_/\/___/  \/____/\/____/
       /\____/
       \_/__/
-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

import Control.Exception (SomeException, displayException, try)
import Control.Monad ((<=<), forM)
import Development.GitRev
import Data.Char (isSpace)
import Data.Either (isRight)
import Data.List (intercalate, isPrefixOf, stripPrefix)
import Data.List.Extra (breakOn)
import Data.List.NonEmpty (NonEmpty, toList)
import Data.Maybe (fromMaybe)
import Data.Semigroup ((<>))
import Data.Version (showVersion)
import System.Exit

import System.Directory (getAppUserDataDirectory, getCurrentDirectory)
import System.FilePath (takeFileName)
import System.FilePath.Posix (takeBaseName)
import "Glob" System.FilePath.Glob (glob)
import Options.Applicative
import Options.Applicative.Help.Pretty (string)

import LLVM.Target
import LLVM.Module
import LLVM.Internal.Context

import Language.Granule.Checker.Checker
import Language.Granule.Checker.Monad (CheckerError)
import Language.Granule.Codegen.Compile (compile)
import Language.Granule.Syntax.Preprocessor
import Language.Granule.Syntax.Preprocessor.Ascii
import Language.Granule.Syntax.Parser
import Language.Granule.Syntax.Pretty
import Language.Granule.Utils
import Paths_granule_compiler (version)

main :: IO ()
main = do
    (globPatterns, config) <- getGrConfig
    if null globPatterns
      then runGrOnStdIn config
      else runGrOnFiles globPatterns config

-- | Run the checker and interpreter on a bunch of files
runGrOnFiles :: [FilePath] -> GrConfig -> IO ()
runGrOnFiles globPatterns config = let ?globals = grGlobals config in do
    pwd <- getCurrentDirectory
    results <- forM globPatterns $ \pattern -> do
      paths <- glob pattern
      case paths of
        [] -> do
          let result = Left $ NoMatchingFiles pattern
          printResult result
          return [result]
        _ -> forM paths $ \path -> do
          let fileName = if pwd `isPrefixOf` path then takeFileName path else path
          let ?globals = ?globals{ globalsSourceFilePath = Just fileName } in do
            printInfo $ "Checking " <> fileName <> "..."
            src <- preprocess
              (rewriter config)
              (keepBackup config)
              path
              (literateEnvName config)
            result <- run src
            printResult result
            return result
    if all isRight (concat results) then exitSuccess else exitFailure

runGrOnStdIn :: GrConfig -> IO ()
runGrOnStdIn GrConfig{..}
  = let ?globals = grGlobals{ globalsSourceFilePath = Just "stdin" } in do
      printInfo "Reading from stdin: confirm input with `enter+ctrl-d` or exit with `ctrl-c`"
      debugM "Globals" (show ?globals)
      result <- getContents >>= run
      printResult result
      if isRight result then exitSuccess else exitFailure

-- print the result of running the checker and interpreter
printResult
  :: (?globals :: Globals)
  => Either CompileError CompileResult
  -> IO ()
printResult = \case
    Left err -> printError err
    Right CompileSuccess -> printSuccess "Compiled!"

{-| Run the input through the type checker and evaluate.
-}
run
  :: (?globals :: Globals)
  => String
  -> IO (Either CompileError CompileResult)
run input = let ?globals = fromMaybe mempty (grGlobals <$> getEmbeddedGrFlags input) <> ?globals in do
    result <- try $ parseAndDoImportsAndFreshenDefs input
    case result of
      Left (e :: SomeException) -> return . Left . ParseError $ show e
      Right ast -> do
        -- Print to terminal when in debugging mode:
        debugM "Pretty-printed AST:" $ pretty ast
        debugM "Raw AST:" $ show ast
        -- Check and evaluate
        checked <- try $ check ast
        case checked of
          Left (e :: SomeException) -> return .  Left . FatalError $ displayException e
          Right (Left errs) -> return . Left $ CheckerError errs
          Right (Right ast') -> do
            printSuccess "OK, compiling..."
            let moduleName = takeBaseName $ sourceFilePath
            case compile moduleName ast' of
              Left (e :: String) ->
                return $ Left $ CompileError e
              Right moduleAST -> do
                withHostTargetMachine $ \machine ->
                  withContext $ \context ->
                    withModuleFromAST context moduleAST $ \mo -> do
                      writeBitcodeToFile (File (moduleName ++ ".bc")) mo
                      writeObjectToFile machine (File (moduleName ++ ".o")) mo
                return $ Right $ CompileSuccess


-- | Get the flags embedded in the first line of a file, e.g.
-- "-- gr --no-eval"
getEmbeddedGrFlags :: String -> Maybe GrConfig
getEmbeddedGrFlags
  = foldr (<|>) Nothing
  . map getEmbeddedGrFlagsLine
  . take 3 -- only check for flags within the top 3 lines (so they are visible and at the top)
  . lines
  where
    getEmbeddedGrFlagsLine
      = parseGrFlags . dropWhile isSpace
      <=< stripPrefix "gr" . dropWhile isSpace
      <=< stripPrefix "--" . dropWhile isSpace


parseGrFlags :: String -> Maybe GrConfig
parseGrFlags
  = pure . snd
  <=< getParseResult . execParserPure (prefs disambiguate) parseGrConfig . words


data GrConfig = GrConfig
  { grRewriter    :: Maybe (String -> String)
  , grKeepBackup      :: Maybe Bool
  , grLiterateEnvName :: Maybe String
  , grGlobals         :: Globals
  }

rewriter :: GrConfig -> Maybe (String -> String)
rewriter c = grRewriter c <|> Nothing

keepBackup :: GrConfig -> Bool
keepBackup = fromMaybe False . grKeepBackup

literateEnvName :: GrConfig -> String
literateEnvName = fromMaybe "granule" . grLiterateEnvName

instance Semigroup GrConfig where
  c1 <> c2 = GrConfig
    { grRewriter    = grRewriter    c1 <|> grRewriter  c2
    , grKeepBackup      = grKeepBackup      c1 <|> grKeepBackup      c2
    , grLiterateEnvName = grLiterateEnvName c1 <|> grLiterateEnvName c2
    , grGlobals         = grGlobals         c1 <>  grGlobals         c2
    }

instance Monoid GrConfig where
  mempty = GrConfig
    { grRewriter    = Nothing
    , grKeepBackup      = Nothing
    , grLiterateEnvName = Nothing
    , grGlobals         = mempty
    }

getGrConfig :: IO ([FilePath], GrConfig)
getGrConfig = do
    (globPatterns, configCLI) <- getGrCommandLineArgs
    configHome <- readUserConfig (grGlobals configCLI)
    pure (globPatterns, configCLI <> configHome)
  where
  -- TODO: UNIX specific
    readUserConfig :: Globals -> IO GrConfig
    readUserConfig globals = do
      let ?globals = globals
      try (getAppUserDataDirectory "granule") >>= \case
        Left (e :: SomeException) -> do
          debugM "Read user config" $ show e
          pure mempty
        Right configFile ->
          try (parseGrFlags <$> readFile configFile) >>= \case
            Left (e :: SomeException) -> do
              debugM "Read user config" $ show e
              pure mempty
            Right Nothing -> do
              printInfo . red . unlines $
                [ "Couldn't parse granule configuration file at " <> configFile
                , "Run `gr --help` to see a list of accepted flags."
                ]
              pure mempty
            Right (Just config) -> pure config


getGrCommandLineArgs :: IO ([FilePath], GrConfig)
getGrCommandLineArgs = customExecParser (prefs disambiguate) parseGrConfig

parseGrConfig :: ParserInfo ([FilePath], GrConfig)
parseGrConfig = info (go <**> helper) $ briefDesc
    <> (headerDoc . Just . string . unlines)
            [ "The Granule Interpreter"
            , "version: "     <> showVersion version
            , "branch: "      <> $(gitBranch)
            , "commit hash: " <> $(gitHash)
            , "commit date: " <> $(gitCommitDate)
            , if $(gitDirty) then "(uncommitted files present)" else ""
            ]
    <> footer "This software is provided under a BSD3 license and comes with NO WARRANTY WHATSOEVER.\
              \ Consult the LICENSE for further information."
  where
    go = do
        globPatterns <-
          many $ argument str $ metavar "GLOB_PATTERNS" <> action "file"
          <> (help . unwords)
            [ "Glob pattern for Granule source files. If the file extension is `.md`/`.tex`, the markdown/TeX preprocessor will be used."
            , "If none are given, input will be read from stdin."
            ]

        globalsDebugging <-
          flag Nothing (Just True)
            $ long "debug"
            <> help "Debug mode"

        globalsSuppressInfos <-
          flag Nothing (Just True)
            $ long "no-info"
            <> help "Don't output info messages"

        globalsSuppressErrors <-
          flag Nothing (Just True)
            $ long "no-error"
            <> help "Don't output error messages"

        globalsNoColors <-
          flag Nothing (Just True)
            $ long "no-color"
            <> long "no-colour"
            <> help "Turn off colors in terminal output"

        globalsAlternativeColors <-
          flag Nothing (Just True)
            $ long "alternative-colors"
            <> long "alternative-colours"
            <> help "Print success messages in blue instead of green (may help with color blindness)"

        globalsNoEval <-
          flag Nothing (Just True)
            $ long "no-eval"
            <> help "Don't evaluate, only type-check"

        globalsTimestamp <-
          flag Nothing (Just True)
            $ long "timestamp"
            <> help "Print timestamp in info and error messages"

        globalsSolverTimeoutMillis <-
          (optional . option (auto @Integer))
            $ long "solver-timeout"
            <> (help . unwords)
            [ "SMT solver timeout in milliseconds (negative for unlimited)"
            , "Defaults to"
            , show solverTimeoutMillis <> "ms."
            ]

        globalsIncludePath <-
          optional $ strOption
            $ long "include-path"
            <> help ("Path to the standard library. Defaults to "
                    <> show includePath)
            <> metavar "PATH"

        globalsEntryPoint <-
          optional $ strOption
            $ long "entry-point"
            <> help ("Program entry point. Defaults to " <> show entryPoint)
            <> metavar "ID"

        grRewriter
          <- flag'
            (Just asciiToUnicode)
            (long "ascii-to-unicode" <> help "WARNING: Destructively overwrite ascii characters to multi-byte unicode.")
          <|> flag Nothing
            (Just unicodeToAscii)
            (long "unicode-to-ascii" <> help "WARNING: Destructively overwrite multi-byte unicode to ascii.")

        grKeepBackup <-
          flag Nothing (Just True)
            $ long "keep-backup"
            <> help "Keep a backup copy of the input file (only has an effect when destructively preprocessing.)"

        grLiterateEnvName <-
          optional $ strOption
            $ long "literate-env-name"
            <> help ("Name of the code environment to check in literate files. Defaults to "
                    <> show (literateEnvName mempty))

        pure
          ( globPatterns
          , GrConfig
            { grRewriter
            , grKeepBackup
            , grLiterateEnvName
            , grGlobals = Globals
              { globalsDebugging
              , globalsNoColors
              , globalsAlternativeColors
              , globalsNoEval
              , globalsSuppressInfos
              , globalsSuppressErrors
              , globalsTimestamp
              , globalsTesting = Nothing
              , globalsSolverTimeoutMillis
              , globalsIncludePath
              , globalsSourceFilePath = Nothing
              , globalsEntryPoint
              }
            }
          )
      where
        ?globals = mempty @Globals

data CompileResult = CompileSuccess

data CompileError
  = ParseError String
  | CheckerError (NonEmpty CheckerError)
  | CompileError String
  | FatalError String
  | NoEntryPoint
  | NoMatchingFiles String
  deriving Show

instance UserMsg CompileError where
  title ParseError {} = "Parse error"
  title CheckerError {} = "Type checking failed"
  title CompileError {} = "Error during compilation"
  title FatalError{} = "Fatal error"
  title NoEntryPoint{} = "No program entry point"
  title NoMatchingFiles{} = "User error"

  msg (ParseError m) = fst . breakOn "CallStack (from HasCallStack):" $ m -- TODO
  msg (CheckerError ms) = intercalate "\n\n" . map formatError . toList $ ms
  msg (CompileError m) = m
  msg (FatalError m) = m
  msg NoEntryPoint = "Program entry point `" <> entryPoint <> "` not found. A different one can be specified with `--entry-point`."
  msg (NoMatchingFiles p) = "The glob pattern `" <> p <> "` did not match any files."
