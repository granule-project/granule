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

import Control.Exception (SomeException, try)
import Control.Monad (forM)
import Data.List (stripPrefix)
import Data.Semigroup ((<>))
import Data.Version (showVersion)
import System.Exit

import System.Directory (getCurrentDirectory)
import "Glob" System.FilePath.Glob (glob)
import Options.Applicative

import Language.Granule.Checker.Checker
import Paths_granule_compiler (version)
import Language.Granule.Syntax.Parser
import Language.Granule.Syntax.Pretty
import Language.Granule.Utils

import Data.Text.Lazy (unpack)
import LLVM.Pretty (ppllvm)
import LLVM.Target
import LLVM.Module
import LLVM.Internal.Context
import Language.Granule.Codegen.Codegen

main :: IO ()
main = do
  (globPatterns,globals) <- customExecParser (prefs disambiguate) parseArgs
  let ?globals = globals in do
    if null globPatterns then do
      let ?globals = globals { sourceFilePath = "stdin" } in do
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
            let fileName =
                 case currentDir `stripPrefix` p of
                   Just f  -> tail f
                   Nothing -> p

            let ?globals = globals { sourceFilePath = fileName }
            printInfo $ "\nChecking " <> fileName <> "..."
            run =<< readFile p
      if all (== ExitSuccess) (concat results) then exitSuccess else exitFailure


{-| Run the input through the type checker and evaluate.
-}
run :: (?globals :: Globals) => String -> IO ExitCode
run input = do
  result <- try $ parseDefs input
  case result of
    Left (e :: SomeException) -> do
      printErr $ ParseError $ show e
      return (ExitFailure 1)

    Right ast -> do
      -- Print to terminal when in debugging mode:
      debugM "AST" (show ast)
      debugM "Pretty-printed AST:" $ pretty ast
      -- Check and evaluate
      checked <- try $ check ast
      case checked of
        Left (e :: SomeException) -> do
          printErr $ CheckerError $ show e
          return (ExitFailure 1)
        Right Failed -> do
          printInfo "Failed" -- specific errors have already been printed
          return (ExitFailure 1)
        Right Ok -> do
          if noEval ?globals then do
            printInfo $ green "Ok"
            return ExitSuccess
          else do
            printInfo $ green "Ok, evaluating..."
            let result = codegen ast
            case result of
              Left (e :: SomeException) -> do
                printErr $ EvalError $ show e
                return (ExitFailure 1)
              Right irModuleAst -> do
                printInfo "Compiled Successfully"
                printInfo (unpack (ppllvm irModuleAst))
                withHostTargetMachine $ \machine ->
                    withContext $ \context -> do
                        withModuleFromAST context irModuleAst (writeObjectToFile machine (File "out.o"))
                return ExitSuccess


parseArgs :: ParserInfo ([FilePath],Globals)
parseArgs = info (go <**> helper) $ briefDesc
    <> header ("Granule " <> showVersion version)
    <> footer "\n\nThis software is provided under a BSD3 license and comes with NO WARRANTY WHATSOEVER.\
              \ Consult the LICENSE for further information."
  where
    go = do
        files <- many $ argument str $ metavar "SOURCE_FILES..."
        debugging <-
          switch $ long "debug" <> short 'd' <> help "(D)ebug mode"
        suppressInfos <-
          switch $ long "no-infos" <> short 'i' <> help "Don't output (i)nfo messages"
        suppressErrors <-
          switch $ long "no-errors" <> short 'e' <> help "Don't output (e)rror messages"
        noColors <-
          switch $ long "no-colors" <> short 'c' <> help "Turn off (c)olors in terminal output"
        noEval <-
          switch $ long "no-eval" <> short 't' <> help "Don't evaluate, only (t)ype-check"
        timestamp <-
          switch $ long "timestamp" <> help "Print timestamp in info and error messages"
        pure (files, defaultGlobals { debugging, noColors, noEval, suppressInfos, suppressErrors, timestamp })

data RuntimeError
  = ParseError String
  | CheckerError String
  | EvalError String
  | GenericError String

instance UserMsg RuntimeError where
  title ParseError {} = "Error during parsing"
  title CheckerError {} = "Error during type checking"
  title EvalError {} = "Error during evaluation"
  title GenericError {} = "Error"
  msg (ParseError m) = m
  msg (CheckerError m) = m
  msg (EvalError m) = m
  msg (GenericError m) = m
