{-# LANGUAGE ImplicitParams #-}

import Data.ByteString.Lazy.Char8 (pack)
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString, findByExtension)
import System.FilePath (takeBaseName, replaceExtension)
import System.IO.Silently (capture_)

import qualified Language.Granule.Interpreter as Interpreter
import Language.Granule.Utils (Globals (..))

main :: IO ()
main = defaultMain =<< goldenTests

goldenTests :: IO TestTree
goldenTests = do
  files <- findByExtension [".gr", ".gr.md"] ".."
  return $ testGroup "Granule golden tests"
    [ goldenVsString
        (takeBaseName file) -- test name
        (replaceExtension file ".output") -- golden file path
        (pack <$> runGranule file) -- action whose result is tested
    | file <- files
    ]
  where
    runGranule :: String -> IO String
    runGranule f = let ?globals = globals in do
      src <- readFile f
      output <- capture_ (Interpreter.run src)
      return output

    globals :: Globals
    globals = Globals
        { debugging = False
        , sourceFilePath = ""
        , noColors = True
        , noEval = False
        , suppressInfos = False
        , suppressErrors = False
        , timestamp = False
        , solverTimeoutMillis = 5000
        , includePath = "StdLib"
        }