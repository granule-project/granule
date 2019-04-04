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

import Control.Exception (SomeException, try)
import Control.Monad (forM)
import Data.List (stripPrefix)
import Data.Functor.Identity (runIdentity)
import Data.Semigroup ((<>))
import Data.Version (showVersion)
import System.Exit
import Text.Read (readMaybe)

import System.Directory (getAppUserDataDirectory, getCurrentDirectory)
import "Glob" System.FilePath.Glob (glob)
import Options.Applicative

import Language.Granule.Checker.Checker
import Language.Granule.Eval
import Language.Granule.Interpreter.Config
import Language.Granule.Interpreter.Preprocess
import Language.Granule.Rewriter.Rewrite (rewriteWithoutInterfaces)
import qualified Language.Granule.Rewriter.Type as RT
import Language.Granule.Syntax.Parser
import Language.Granule.Syntax.Pretty
import Language.Granule.Utils (Globals, debugM, printInfo, printErr, green)
import qualified Language.Granule.Utils as Utils
import Paths_granule_interpreter (version)


main :: IO ()
main = do
  (globPatterns, cmdlineOpts) <- customExecParser (prefs disambiguate) parseArgs
  config <- defaultConfig . (cmdlineOpts <>) <$> readUserConfig cmdlineOpts
  let globals = toGlobals "" $ config
  let ?globals = globals in do
    if null globPatterns then let ?globals = globals { Utils.sourceFilePath = "stdin" } in do
      printInfo "Reading from stdin: confirm input with `enter+ctrl-d` or exit with `ctrl-c`"
      debugM "Globals" (show globals)
      exitWith =<< run =<< getContents
    else do
      debugM "Globals" (show globals)
      currentDir <- getCurrentDirectory
      results <- forM globPatterns $ \p -> do
        filePaths <- glob p
        case filePaths of
          [] -> do
            printErr $ GenericError $ "The glob pattern `" <> p <> "` did not match any files."
            return [(ExitFailure 1)]
          _ -> forM filePaths $ \p -> do
            let fileName = case currentDir `stripPrefix` p of
                  Just f  -> tail f
                  Nothing -> p

            let ?globals = globals { Utils.sourceFilePath = fileName }
            printInfo $ "\nChecking " <> fileName <> "..."
            src <- preprocess
              (runIdentity $ ascii2unicode config)
              (runIdentity $ keepBackupAscii config)
              p
            run src
      if all (== ExitSuccess) (concat results) then exitSuccess else exitFailure

  where
    -- TODO: UNIX specific
    readUserConfig :: Options Maybe -> IO (Options Maybe)
    readUserConfig cmdlineOpts = do
      let ?globals = toGlobals "" $ defaultConfig cmdlineOpts
      try (getAppUserDataDirectory "granule") >>= \case
        Left (e :: SomeException) -> do
          debugM "Read user config" $ show e
          pure mempty
        Right configFile ->
          try (readMaybe @(Options Maybe) <$> readFile configFile) >>= \case
            Left (e :: SomeException) -> do
              debugM "Read user config" $ show e
              pure mempty
            Right Nothing -> do
              printInfo $ "Couldn't parse granule configuration file at "
                        <> configFile
              pure mempty
            Right (Just os) -> do
              pure os


{-| Run the input through the type checker and evaluate.
-}
run :: (?globals :: Globals) => String -> IO ExitCode
run input = do
  result <- try $ parseAndDoImportsAndFreshenDefs input
  case result of
    Left (e :: SomeException) -> do
      printErr $ ParseError $ show e
      return (ExitFailure 1)

    Right ast -> do
      -- Print to terminal when in debugging mode:
      debugM "Pretty-printed AST:" $ pretty ast
      debugM "Raw AST:" $ show ast
      -- Check and evaluate
      maybeCheckedAst <- try $ check ast
      case maybeCheckedAst of
        Left (e :: SomeException) -> do
          printErr $ CheckerError $ show e
          return (ExitFailure 1)
        Right Nothing -> do
          printInfo "Failed" -- specific errors have already been printed
          return (ExitFailure 1)
        Right (Just (renv, checkedAst)) -> do
          if Utils.noEval ?globals then do
            printInfo $ green "Ok"
            return ExitSuccess
          else do
            printInfo $ green "Ok, evaluating..."
            maybeRewrittenAst <- rewriteWithoutInterfaces renv checkedAst
            case maybeRewrittenAst of
              Left err -> do
                printErr $ RewriterError $ show err
                pure (ExitFailure 1)
              Right rewrittenAst -> do
                result <- try $ eval rewrittenAst
                case result of
                  Left (e :: SomeException) -> do
                    printErr $ EvalError $ show e
                    return (ExitFailure 1)
                  Right Nothing -> do
                    printInfo "There is no `main` definition."
                    return ExitSuccess
                  Right (Just result) -> do
                    printInfo "`main` returned:"
                    putStrLn (pretty result)
                    return ExitSuccess


parseArgs :: ParserInfo ([FilePath], Options Maybe)
parseArgs = info (go <**> helper) $ briefDesc
    <> header ("Granule " <> showVersion version)
    <> footer "\n\nThis software is provided under a BSD3 license and comes with NO WARRANTY WHATSOEVER.\
              \Consult the LICENSE for further information."
  where
    go = do
        files <- many $ argument str $ metavar "SOURCE_FILES..."
        debugging <-
          flag Nothing (Just True)
            $ long "debug"
            <> help "Debug mode"

        suppressInfos <-
          flag Nothing (Just True)
            $ long "no-info"
            <> help "Don't output info messages"

        suppressErrors <-
          flag Nothing (Just True)
            $ long "no-error"
            <> help "Don't output error messages"

        noColors <-
          flag Nothing (Just True)
            $ long "no-color"
            <> help "Turn off colors in terminal output"

        noEval <-
          flag Nothing (Just True)
            $ long "no-eval"
            <> help "Don't evaluate, only type-check"

        timestamp <-
          flag Nothing (Just True)
            $ long "timestamp"
            <> help "Print timestamp in info and error messages"

        solverTimeoutMillis <-
          optional $ option (auto @Integer) (
            long "solver-timeout"
            <> help "SMT solver timeout in milliseconds (negative for unlimited)"
            )

        includePath <-
          optional $ strOption
            $ long "include-path"
            <> help "Path to the standard library"
            <> metavar "PATH"

        ascii2unicode <-
          flag Nothing (Just True)
            $ long "ascii-to-unicode"
            <> help "Destructively rewrite ascii symbols to their unicode equivalents (WARNING: overwrites the input file)"

        keepBackupAscii <-
          flag Nothing (Just True)
            $ long "keep-backup-ascii"
            <> help "Keep a backup copy of the input file (only has an effect when destructively preprocessing with `--ascii-to-unicode`)"

        pure
          ( files
          , Options
            { debugging
            , noColors
            , noEval
            , suppressInfos
            , suppressErrors
            , timestamp
            , solverTimeoutMillis
            , includePath
            , ascii2unicode
            , keepBackupAscii
            }
          )

data RuntimeError
  = ParseError String
  | CheckerError String
  | EvalError String
  | GenericError String
  | RewriterError RT.RewriterError

instance Utils.UserMsg RuntimeError where
  title ParseError {} = "Error during parsing"
  title CheckerError {} = "Error during type checking"
  title EvalError {} = "Error during evaluation"
  title GenericError {} = "Error"
  title RewriterError {} = "Error during rewriting"
  msg (ParseError m) = m
  msg (CheckerError m) = m
  msg (EvalError m) = m
  msg (GenericError m) = m
  msg (RewriterError e) = show e
