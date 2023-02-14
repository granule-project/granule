{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NamedFieldPuns #-}
module Language.Granule.Compiler where

import Control.Exception (SomeException, displayException, try)
import Control.Monad ((<=<), forM_, when)
import Development.GitRev
import Data.Char (isSpace)
import Data.List (isPrefixOf, stripPrefix)
import Data.Maybe (fromMaybe)
import Data.Version (showVersion)

import System.Directory (getAppUserDataDirectory, getCurrentDirectory)
import System.FilePath (takeFileName)
import "Glob" System.FilePath.Glob (glob)
import Options.Applicative
import Options.Applicative.Help.Pretty (string)

import Language.Granule.Checker.Checker
import Language.Granule.Syntax.Def (extendASTWith)
import Language.Granule.Syntax.Preprocessor
import Language.Granule.Syntax.Parser
import Language.Granule.Syntax.Preprocessor.Ascii
import Language.Granule.Syntax.Pretty
import Language.Granule.Utils
import Paths_granule_compiler (version)
import Language.Granule.Compiler.HSCodegen


main :: IO ()
main = do
    (globPatterns, config) <- getGrConfig
    if null globPatterns
    then error "Expected glob pattern"
    else compileGrOnFiles globPatterns config

compileGrOnFiles :: [FilePath] -> GrConfig -> IO ()
compileGrOnFiles globPatterns config = let ?globals = grGlobals config in do
  pwd <- getCurrentDirectory
  forM_ globPatterns $ \pat -> do
    paths <- glob pat
    case paths of
      [] -> error "No matching files"
      _ -> forM_ paths $ \path -> do
        let fileName = if pwd `isPrefixOf` path then takeFileName path else path
        let ?globals = ?globals{ globalsSourceFilePath = Just fileName } in do
          printInfo $ "Checking " <> fileName <> "..."
          src <- preprocess
            (rewriter config)
            (keepBackup config)
            path
            (literateEnvName config)
          hsCode <- compile config src
          debugM "Code: " hsCode
          let outPath = changeFileExtension path
          printSuccess $ "Writing " ++ outPath
          writeFile outPath hsCode

compile
  :: (?globals :: Globals)
  => GrConfig
  -> String
  -> IO String
compile config input = let ?globals = maybe mempty grGlobals (getEmbeddedGrFlags input) <> ?globals in do
  result <- try $ parseAndDoImportsAndFreshenDefs input
  case result of
    Left (e :: SomeException) -> error $ show e
    Right (ast, extensions) ->
      -- update globals with extensions
      let ?globals = ?globals { globalsExtensions = extensions } in do
      -- reject CBN language pragma
      when (CBN `elem` globalsExtensions ?globals) $ error "Cannot compile in CBN mode"
      -- Print to terminal when in debugging mode:
      debugM "Pretty-printed AST:" $ pretty ast
      debugM "Raw AST:" $ show ast
      -- Check and evaluate
      checked <- try $ check ast
      case checked of
        Left (e :: SomeException) -> error $ displayException e
        Right (Left errs) -> do
          error (show errs)
        Right (Right (ast', derivedDefs)) -> do
          printSuccess "Ok, compiling..."
          let ast' = extendASTWith derivedDefs ast
              result = cg ast'
          case result of
            Left e -> error (bold . red . show $ e)
            Right str -> return str

changeFileExtension :: String -> String
changeFileExtension str = reverse (drop 2 $ reverse str) ++ "hs"

getEmbeddedGrFlags :: String -> Maybe GrConfig
getEmbeddedGrFlags
  = foldr (<|>) Nothing
  . map getEmbeddedGrFlagsLine
  . take 3 -- only check for flags within the top 3 lines
  . filter (not . all isSpace)
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
  { grRewriter        :: Maybe (String -> String)
  , grKeepBackup      :: Maybe Bool
  , grLiterateEnvName :: Maybe String
  , grShowVersion     :: Bool
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
    { grRewriter        = grRewriter        c1 <|> grRewriter        c2
    , grKeepBackup      = grKeepBackup      c1 <|> grKeepBackup      c2
    , grLiterateEnvName = grLiterateEnvName c1 <|> grLiterateEnvName c2
    , grGlobals         = grGlobals         c1 <>  grGlobals         c2
    , grShowVersion     = grShowVersion     c1 ||  grShowVersion     c2
    }

instance Monoid GrConfig where
  mempty = GrConfig
    { grRewriter    = Nothing
    , grKeepBackup      = Nothing
    , grLiterateEnvName = Nothing
    , grGlobals         = mempty
    , grShowVersion     = False
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
            [ "The Granule Compiler"
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

        grShowVersion <-
          flag False True
            $ long "version"
            <> help "Show version"

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

        globalsExampleLimit <-
          (optional . option (auto @Int))
            $ long "example-limit"
            <> (help . unwords)
            [ "Limit to the number of times synthed terms should be tried on examples before giving up"
            , "Defaults to"
            , show exampleLimit <> ""
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

        globalsRewriteHoles <-
          flag Nothing (Just True)
            $ long "rewrite-holes"
            <> help "WARNING: Destructively overwrite equations containing holes to pattern match on generated case-splits."

        globalsHoleLine <-
          optional . option (auto @Int)
            $ long "hole-line"
            <> help "The line where the hole you wish to rewrite is located."
            <> metavar "LINE"

        globalsHoleCol <-
          optional . option (auto @Int)
            $ long "hole-column"
            <> help "The column where the hole you wish to rewrite is located."
            <> metavar "COL"

        globalsSynthesise <-
          flag Nothing (Just True)
            $ long "synthesise"
            <> help "Turn on program synthesis. Must be used in conjunction with hole-line and hole-column"

        globalsIgnoreHoles <-
          flag Nothing (Just True)
            $ long "ignore-holes"
            <> help "Suppress information from holes (treat holes as well-typed)"

        globalsHaskellSynth <-
          flag Nothing (Just True)
           $ long "linear-haskell"
            <> help "Synthesise Linear Haskell programs"

        globalsSubtractiveSynthesis <-
          flag Nothing (Just True)
           $ long "subtractive"
            <> help "Use subtractive mode for synthesis, rather than additive (default)."

        globalsAlternateSynthesisMode <-
          flag Nothing (Just True)
           $ long "alternate"
            <> help "Use alternate mode for synthesis (subtractive divisive, additive naive)"

        globalsGradeOnRule <-
          flag Nothing (Just True)
           $ long "gradeonrule"
            <> help "Use alternate grade-on-rule mode for synthesis"

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

        globalsBenchmark <-
          flag Nothing (Just True)
           $ long "benchmark"
           <> help "Compute benchmarking results for the synthesis procedure."

        globalsBenchmarkRaw <-
          flag Nothing (Just True)
           $ long "raw-data"
           <> help "Show raw data of benchmarking data for synthesis."

        pure
          ( globPatterns
          , GrConfig
            { grRewriter
            , grKeepBackup
            , grLiterateEnvName
            , grShowVersion
            , grGlobals = Globals
              { globalsDebugging
              , globalsNoColors
              , globalsAlternativeColors
              , globalsNoEval
              , globalsSuppressInfos
              , globalsSuppressErrors
              , globalsIgnoreHoles
              , globalsTimestamp
              , globalsTesting = Nothing
              , globalsSolverTimeoutMillis
              , globalsIncludePath
              , globalsSourceFilePath = Nothing
              , globalsEntryPoint
              , globalsRewriteHoles
              , globalsHolePosition = (,) <$> globalsHoleLine <*> globalsHoleCol
              , globalsSynthesise
              , globalsBenchmark
              , globalsBenchmarkRaw
              , globalsSubtractiveSynthesis
              , globalsAlternateSynthesisMode
              , globalsGradeOnRule
              , globalsHaskellSynth
              , globalsExampleLimit
              , globalsExtensions = []
              }
            }
          )
      where
        ?globals = mempty @Globals
