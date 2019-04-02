{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Utils where

import Control.Applicative ((<|>))
import Control.Exception (SomeException, catch, try)
import Control.Monad (when, forM)
import Data.List ((\\), nub, sortBy)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Ord
import Data.Time.Clock (getCurrentTime)
import Data.Time.LocalTime (getTimeZone, utc, utcToLocalTime)
import Debug.Trace (trace, traceM)
import System.IO (hPutStrLn, stderr)
import System.IO.Unsafe (unsafePerformIO)
import "Glob" System.FilePath.Glob (glob)

import Language.Granule.Syntax.Span

-- | Flags that change Granule's behaviour
data Globals = Globals
  { globalsDebugging           :: Maybe Bool
  , globalsNoColors            :: Maybe Bool
  , globalsAlternativeColors   :: Maybe Bool
  , globalsNoEval              :: Maybe Bool
  , globalsSuppressInfos       :: Maybe Bool
  , globalsSuppressErrors      :: Maybe Bool
  , globalsTimestamp           :: Maybe Bool
  , globalsTesting             :: Maybe Bool -- ^ whether we are currently running a test (e.g. for pretty printing)
  , globalsSolverTimeoutMillis :: Maybe Integer
  , globalsIncludePath         :: Maybe FilePath
  , globalsSourceFilePath      :: Maybe FilePath
  } deriving (Read, Show)

-- | Accessors for global flags with default values
debugging, noColors, alternativeColors, noEval, suppressInfos, suppressErrors,
  timestamp, testing :: (?globals :: Globals) => Bool
debugging         = fromMaybe False $ globalsDebugging ?globals
noColors          = fromMaybe False $ globalsNoColors ?globals
alternativeColors = fromMaybe False $ globalsAlternativeColors ?globals
noEval            = fromMaybe False $ globalsNoEval ?globals
suppressInfos     = fromMaybe False $ globalsSuppressInfos ?globals
suppressErrors    = fromMaybe False $ globalsSuppressErrors ?globals
timestamp         = fromMaybe False $ globalsTimestamp ?globals
testing           = fromMaybe False $ globalsTesting ?globals

-- | Accessor for the solver timeout with a default value
solverTimeoutMillis :: (?globals :: Globals) => Integer
solverTimeoutMillis = fromMaybe 5000 $ globalsSolverTimeoutMillis ?globals

-- | Accessors for global file paths with default values
includePath, sourceFilePath :: (?globals :: Globals) => FilePath
includePath         = fromMaybe "StdLib" $ globalsIncludePath ?globals
sourceFilePath      = fromMaybe ""       $ globalsSourceFilePath ?globals

-- | Merge two 'Globals', giving preference to the settings of the left one
instance Semigroup Globals where
  g1 <> g2 = Globals
      { globalsDebugging           = globalsDebugging           g1 <|> globalsDebugging           g2
      , globalsNoColors            = globalsNoColors            g1 <|> globalsNoColors            g2
      , globalsAlternativeColors   = globalsAlternativeColors   g1 <|> globalsAlternativeColors   g2
      , globalsNoEval              = globalsNoEval              g1 <|> globalsNoEval              g2
      , globalsSuppressInfos       = globalsSuppressInfos       g1 <|> globalsSuppressInfos       g2
      , globalsSuppressErrors      = globalsSuppressErrors      g1 <|> globalsSuppressErrors      g2
      , globalsTimestamp           = globalsTimestamp           g1 <|> globalsTimestamp           g2
      , globalsSolverTimeoutMillis = globalsSolverTimeoutMillis g1 <|> globalsSolverTimeoutMillis g2
      , globalsIncludePath         = globalsIncludePath         g1 <|> globalsIncludePath         g2
      , globalsSourceFilePath      = globalsSourceFilePath      g1 <|> globalsSourceFilePath      g2
      , globalsTesting             = globalsTesting             g1 <|> globalsTesting             g2
      }

instance Monoid Globals where
  mempty = Globals
    { globalsDebugging           = Nothing
    , globalsNoColors            = Nothing
    , globalsAlternativeColors   = Nothing
    , globalsNoEval              = Nothing
    , globalsSuppressInfos       = Nothing
    , globalsSuppressErrors      = Nothing
    , globalsTimestamp           = Nothing
    , globalsSolverTimeoutMillis = Nothing
    , globalsIncludePath         = Nothing
    , globalsSourceFilePath      = Nothing
    , globalsTesting             = Nothing
    }

-- | A class for messages that are shown to the user. TODO: make more general
class UserMsg a where
  -- | The title of the message
  title :: a -> String

  -- | The location (defaults to 'nullSpan')
  location :: (?globals :: Globals) => a -> Span
  location _ = nullSpan

  -- | The body of the message
  msg :: (?globals :: Globals) => a -> String


-- | Make a span from a pair of positions
mkSpan :: (?globals :: Globals) => (Pos, Pos) -> Span
mkSpan (start, end) = Span start end sourceFilePath

-- | When a source location is not applicable
nullSpan :: (?globals :: Globals) => Span
nullSpan = Span (0, 0) (0, 0) sourceFilePath


debugM :: (?globals :: Globals, Applicative f) => String -> String -> f ()
debugM explanation message =
    when debugging $ traceM $
      ((unsafePerformIO getTimeString) <> (bold $ cyan $ "Debug: ") <> explanation <> " \n") <> message <> "\n"

-- | Print to terminal when debugging e.g.:
-- foo x y = x + y `debug` "foo" $ "given " <> show x <> " and " <> show y
debug :: (?globals :: Globals) => a -> String -> a
debug x message
  | debugging = ((unsafePerformIO getTimeString) <> (bold $ magenta $ "Debug: ") <> message <> "\n") `trace` x
  | otherwise = x

printError :: (?globals :: Globals, UserMsg msg) => msg -> IO ()
printError message = when (not suppressErrors) $
  hPutStrLn stderr $ formatError message

printSuccess :: (?globals :: Globals) => String -> IO ()
printSuccess message = when (not suppressInfos)
  (putStrLn . (if alternativeColors then blue else green) $ message)

printInfo :: (?globals :: Globals) => String -> IO ()
printInfo message = when (not suppressInfos) (putStrLn message)

-- printInfo :: (?globals :: Globals) => String -> IO ()
-- printInfo message =
--     when (not $ suppressInfos ?globals) $ do
--       time <- getTimeString
--       putStr $ time <> message

formatError :: (?globals :: Globals, UserMsg msg) => msg -> String
formatError = formatMessage (bold . red)
-- | Given a function to format the title of a message, format the message
-- and its body. e.g. @formatMessage (bold . red)@ for errors.
formatMessage :: (?globals :: Globals, UserMsg msg)
  => (String -> String) -> msg -> String
formatMessage titleStyle message
  = (titleStyle $ title message <> ": ")
    <> sourceFile <> lineCol <> "\n"
    <> msg message
  where
    sourceFile = case filename $ location message of -- sourceFilePath ?globals
      "" -> ""
      p  -> p <> ":"
    lineCol = case location message of
      (Span (0,0) (0,0) _) -> ""
      (Span (line,col) _ _) -> show line <> ":" <> show col <> ":"

formatMessageTime :: (?globals :: Globals, UserMsg msg)
  => (String -> String) -> msg -> IO String
formatMessageTime titleStyle message = do
    time <- getTimeString
    pure $ time <> formatMessage titleStyle message

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
    if noColors
      then message
      else "\ESC[" <> colorCode <> ";1m" <> message <> reset
  where
    reset = "\ESC[0m"

getTimeString :: (?globals :: Globals) => IO String
getTimeString =
    if not timestamp then return ""
    else do
      time <- try getCurrentTime
      case time of
        Right time -> do
          timeZone <-
            catch
              (getTimeZone time) $
              \(e :: SomeException) -> do
                debugM "getTimeZone failed" (show e)
                return utc
          let localTime = utcToLocalTime timeZone time
          return $ show localTime <> ": "
        Left (e :: SomeException) -> do
          debugM "getCurrentTime failed" (show e)
          return ""

-- Extracted from the else in  main from Main.hs for use as a generic function
-- where e is some error handler and f is what is done with each file
processFiles :: [FilePath] -> (FilePath -> IO a) -> (FilePath -> IO a) -> IO [[a]]
processFiles globPatterns e f = forM globPatterns $ (\p -> do
    filePaths <- glob p
    case filePaths of
        [] -> (e p) >>= (return.(:[]))
        _ -> forM filePaths f)

lookupMany :: Eq a => a -> [(a, b)] -> [b]
lookupMany _ []                     = []
lookupMany a' ((a, b):xs) | a == a' = b : lookupMany a' xs
lookupMany a' (_:xs)                = lookupMany a' xs

-- | Get set of duplicates in a list.
-- >>> duplicates [1,2,2,3,3,3]
-- [2,3]
duplicates :: Eq a => [a] -> [a]
duplicates xs = nub (xs \\ nub xs)

-- | Using a projection function to get a partial order on elements, return the
-- groups of duplicates according to the projection. Useful for instance for
-- finding duplicate definitions by projecting on their source names.
--
-- >>> duplicatesBy fst [("alice",1), ("bob",2), ("alice",3), ("alice", 4)]
-- [(("alice",3),("alice",1) :| [("alice",4)])]
--
-- Observe that the second occurrence is the 'fst' element, since we can say
-- that this is the first offending case. The types ensure that we actually
-- have at least 2 instances of the thing we want to duplicate check.
duplicatesBy :: Ord b => (a -> b) -> [a] -> [(a,NonEmpty a)]
duplicatesBy proj
  = mapMaybe (\case x1 :| x2 : xs -> Just (x2, x1 :| xs); _ -> Nothing)
  . NonEmpty.groupBy (\x1 x2 -> proj x1 == proj x2)
  . sortBy (comparing proj)
