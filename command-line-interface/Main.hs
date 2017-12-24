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

import Control.Exception (SomeException, try)
import Control.Monad (forM)
import Data.List (intercalate)
import Data.Semigroup ((<>))
import Data.Version (showVersion)
import System.Exit

import System.FilePath.Glob (glob)
import Options.Applicative

import Checker.Checker
import Eval
import Paths_granule (version)
import Syntax.Parser
import Syntax.Pretty
import Utils


main :: IO ()
main = do
  (globPatterns,globals) <- customExecParser (prefs disambiguate) parseArgs
  if null globPatterns then do
    let ?globals = globals { sourceFilePath = "stdin" }
    printInfo "Reading from stdin: confirm input with `enter+ctrl-d` or exit with `ctrl-c`"
      >> debugM "Globals" (show globals)
    exitWith =<< run =<< getContents
  else do
    let ?globals = globals
    debugM "Globals" (show globals)
    results <- forM globPatterns $ \p -> do
      filePaths <- glob p
      forM filePaths $ \p -> do
        let ?globals = globals { sourceFilePath = p }
        printInfo $ "\nChecking " <> p <> "..."
        run =<< readFile p
    if all (== ExitSuccess) (concat results) then exitSuccess else exitFailure


{-| Run the input through the type checker and evaluate.
-}
run :: (?globals :: Globals) => String -> IO ExitCode
run input = do
  result <- try $ parseDefs input
  case result of
    Left (e :: SomeException) -> do
      printInfo $ "Error during parsing: " <> show e
      return (ExitFailure 3)

    Right (ast, nameMap) -> do
      -- Print to terminal when in debugging mode:
      debugM "AST" $ "[" <> intercalate ",\n\n" (map show ast) <> "]"
      debugM "Pretty-printed AST:" $ show (intercalate "\n\n" $ map pretty ast)
      debugM "Name map" $ show nameMap
      -- Check and evaluate
      checked <- try $ check ast nameMap
      case checked of
        Left (e :: SomeException) -> do
          printInfo $ "Error during type checking: " <> show e
          return (ExitFailure 2)
        Right Failed -> do
          printInfo "Failed"
          return (ExitFailure 1)
        Right Ok -> do
          if noEval ?globals then do
            printInfo $ green "Ok"
            return ExitSuccess
          else do
            printInfo $ green "Ok, evaluating..."
            result <- try $ eval ast
            case result of
              Left (e :: SomeException) -> do
                printInfo $ "Error during evaluation: " <> show e
                return (ExitFailure 4)
              Right Nothing -> do
                printInfo "(No output)"
                return ExitSuccess
              Right (Just result) -> do
                putStrLn (pretty result)
                return ExitSuccess


parseArgs :: ParserInfo ([FilePath],Globals)
parseArgs = info (go <**> helper) $ fullDesc <> header ("Granule " <> showVersion version)
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
        pure (files, defaultGlobals { debugging, noColors, noEval, suppressInfos, suppressErrors })
