{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}

module Utils
-- (
--   Globals, defaultGlobals
-- )
where

import Control.Monad (when)
import Data.Semigroup ((<>))
import Debug.Trace (trace, traceM)
import System.IO (hPutStrLn, stderr)

import Syntax.Expr (Span, Pos, getSpan)
import Syntax.FirstParameter

data Globals =
  Globals {
    debugging :: Bool,
    sourceFilePath :: String,
    noColors :: Bool,
    noEval :: Bool,
    suppressInfos :: Bool,
    suppressErrors :: Bool
  } deriving Show

defaultGlobals :: Globals
defaultGlobals =
    Globals {
      debugging = False,
      sourceFilePath = "",
      noColors = False,
      noEval = False,
      suppressInfos = False,
      suppressErrors = False
    }

class UserMsg a where
  title :: a -> String
  location :: a -> Maybe Span
  msg :: a -> String -- short for `message`, not `monosodium glutamate`

debugM :: (?globals :: Globals, Applicative f) => String -> String -> f ()
debugM explanation message =
    when (debugging ?globals) $ traceM $
      (bold $ cyan $ "Debug: " <> explanation <> " \n") <> message <> "\n"

-- | Print to terminal when debugging e.g.:
-- foo x y = x + y `debug` "foo" $ "given " <> show x <> " and " <> show y
debug :: (?globals :: Globals) => a -> String -> a
debug x message =
    if debugging ?globals
      then ((bold $ magenta $ "Debug: ") <> message <> "\n") `trace` x
      else x

printErr :: (?globals :: Globals, UserMsg msg) => msg -> IO ()
printErr err = when (not $ suppressErrors ?globals) $ hPutStrLn stderr $
    (bold $ red $ title err <> ": ")
    <> sourceFilePath ?globals <> lineCol <> ":\n"
    <> indent (msg err)
  where
    lineCol =
        case location err of
          Nothing -> ""
          Just ((line,col),_) -> ":" <> show line <> ":" <> show col

printInfo :: (?globals :: Globals) => String -> IO ()
printInfo message =  when (not $ suppressInfos ?globals) $ putStrLn $ message

-- backgColor colorCode = txtColor (colorCode + 10)
bold :: (?globals :: Globals) => String -> String
bold = txtColor "1"

black, red, green, yellow, blue, magenta, cyan, white :: (?globals :: Globals) => String -> String
black = txtColor "30"
red = txtColor "31"
green = txtColor "32"
yellow = txtColor "33"
blue = txtColor "34"
magenta = txtColor "35"
cyan = txtColor "36"
white = txtColor "37"

txtColor :: (?globals :: Globals) => String -> String -> String
txtColor colorCode message =
    if noColors ?globals
      then message
      else "\ESC[" <> colorCode <> ";1m" <> message <> reset
  where
    reset = "\ESC[0m"

indent :: String -> String
indent message = "  " <> message
