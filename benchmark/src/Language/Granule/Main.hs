{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-
This tool is for quantitatively evaluating the --synthesis feature
of Granule and constructing a LaTeX table with the results
-}

module Language.Granule.Main where

import System.Process (system)
import System.Exit
import System.Directory (listDirectory, removeFile, doesDirectoryExist, getDirectoryContents)
import System.FilePath.Posix ((</>))
import Control.Monad (forM_, forM, foldM, replicateM, when, unless)
import Data.List (isPrefixOf, isSuffixOf, unwords, intersperse, sort, intercalate, transpose)
import Data.Text (replace, pack, unpack, isInfixOf)
import Data.Maybe (mapMaybe, fromMaybe)
import GHC.Exts (the)
import System.IO
import Text.Printf
import Language.Granule.StdError
import Language.Granule.Benchmarks
import qualified Data.Time as T
import qualified System.IO.Strict as SIO
import System.Environment (getArgs)

import Language.Granule.Benchmarks 


data Measurement = Measurement {
     smtCalls        :: Integer
   , synthTime       :: Double -- greater than the prover time
   , proverTime      :: Double -- greater than the solver time
   , solverTime      :: Double
   , meanTheoremSize :: Double
   , success         :: Bool
   , timeout         :: Bool
   , pathsExplored   :: Integer
    -- To extend with other info...
   }
   deriving (Read, Show)

class Report a where
  report :: ([Measurement], Measurement) -> (Measurement -> a) -> IO ()
  report1 :: ([Measurement], Measurement) -> (Measurement -> a) -> IO ()
  reportLead :: ([Measurement], Measurement) -> (Measurement -> a) -> IO ()
  reportString :: ([Measurement], Measurement) -> (Measurement -> a) -> String
  report1String :: ([Measurement], Measurement) -> (Measurement -> a) -> String


instance Report Bool where
  report (_, aggregate) view | view aggregate = putStr "\\success{}"
                             | otherwise      = putStr "\\fail{} "
  report1 = report
  reportLead = report

  reportString (_, aggregate) view | view aggregate = "\\success{}"
                                   | otherwise      = "\\fail{} "
  report1String = reportString

instance Report Integer where
  report (_, aggregate) view =
    printf "%3d      " (view aggregate)
  report1 = report
  reportLead = report
  reportString (_, aggregate) view =
    printf "%3d      " (view aggregate)
  report1String = reportString

instance Report Double where
  report (results, aggregate) view =
    printf "%6.2f (\\stderr{%6.2f})" (view aggregate) (stdError $ map view results)
  reportLead (results, aggregate) view =
    printf "{\\highlight{$ %6.2f (\\stderr{%6.2f}) $}}" (view aggregate) (stdError $ map view results)
  report1 (_, aggregate) view =
    printf "%6.2f" (view aggregate)
  reportString (results, aggregate) view =
    printf "%6.2f (\\stderr{%6.2f})" (view aggregate) (stdError $ map view results)
  report1String (_, aggregate) view =
    printf "%6.2f" (view aggregate)

modes :: [(String, (String, String))]
modes = [
      ("graded", ("Graded", ""))
    , ("ungraded", ("Ungraded", ""))
--  , ("addp", ("Additive pruning", "--alternate"))
--  , ("sub", ("Subtractive", "--subtractive"))
--  , ("addg", ("Additive - grade-on-rule", " --gradeonrule"))
--  , ("addpg", ("Additive pruning - grade-on-rule", "--alternate --gradeonrule"))
--  , ("subg", ("Subtractive - grade-on-rule", "--subtractive --gradeonrule"))
--  , ("add'", ("Additive - new-structuring", " --altsynthstructuring"))
--  , ("addp'", ("Additive pruning - newstructuring", "--alternate --altsynthstructuring"))
--  , ("sub'", ("Subtractive - new-structuring", "--subtractive --altsynthstructuring"))
--  , ("addg'", ("Additive - grade-on-rule new-structuring", " --gradeonrule --altsynthstructuring"))
--  , ("addpg'", ("Additive pruning - grade-on-rule new-structuring", "--alternate --gradeonrule --altsynthstructuring"))
--  , ("subg'", ("Subtractive - grade-on-rule new-structuring", "--subtractive --gradeonrule --altsynthstructuring"))]
-- , ("subd", ("Subtractive with division", "--subtractive --alternate"))
      ]

defaultRepeatTrys = 10

getRecursiveContents :: FilePath -> IO [FilePath]
getRecursiveContents topPath = do
  names <- getDirectoryContents topPath
  let
    properNames =
      filter (`notElem` [".", ".."]) names
  paths <- forM properNames $ \name -> do
    let path = topPath </> name
    isDirectory <- doesDirectoryExist path
    if isDirectory
      then getRecursiveContents path
      else return [path]
  return (concat paths)


fileArgs :: [String] -> ([String], [String])
fileArgs [] = ([], [])
fileArgs (arg:args) 
  | "--" `isPrefixOf` arg = ([], arg:args)
  | "-" `isPrefixOf` arg  = ([], arg:args)
  | otherwise = let (files, args') = fileArgs args
                in (arg:files, args')


processArgs :: [String] 
            -> ([String] {- Files -}, [String] {- Categories -}, Bool {- FilesPerMode -}, Int {- Repeat -})
processArgs [] = ([], [], False, defaultRepeatTrys)
processArgs (arg:args) 
  | arg == "--categories" = 
      let (categories, args') = fileArgs args 
          (files, categories', fpm, repeats) = processArgs args' 
      in (files, categories ++ categories', fpm, repeats) 
  | arg == "-c" = 
      let (categories, args') = fileArgs args 
          (files, categories', fpm, repeats) = processArgs args' 
      in (files, categories ++ categories', fpm, repeats) 
  | arg == "--files" =
      let (files, args') = fileArgs args 
          (files', categories, fpm, repeats) = processArgs args' 
      in (files ++ files', categories, fpm, repeats)
  | arg == "-f" =
      let (files, args') = fileArgs args 
          (files', categories, fpm, repeats) = processArgs args' 
      in (files ++ files', categories, fpm, repeats)
  | arg == "--per-mode" = 
      let (files, categories, fpm, repeats) = processArgs args 
      in (files, categories, True, repeats)
  | arg == "-p" = 
      let (files, categories, fpm, repeats) = processArgs args 
      in (files, categories, True, repeats)
  | arg == "--repeats" =
      case args of 
        (arg':args') -> 
          let (files, categories, fpm, repeats) = processArgs args'
          in (files, categories, fpm, fromInteger $ read arg')
        _ -> error "--repeats must be given an integer argument"
  | arg == "-n" = 
      case args of 
        (arg':args') -> 
          let (files, categories, fpm, repeats) = processArgs args'
          in (files, categories, fpm, fromInteger $ read arg')
        _ -> error "-n must be given an integer argument"
  | otherwise = error $ printUsage 

printUsage :: String
printUsage = ""


main :: IO ()
main = do
  argsMain <- getArgs
  hFlush stdout
  -- Get current time for log file name
  currentTime <- T.getCurrentTime
  let logIdent = T.formatTime T.defaultTimeLocale "%F-%H-%M" currentTime

  (files, categories, fpm, repeatTimes) <- return $ processArgs argsMain

  items <- return $
    case (files, categories) of 
      ([], []) -> (benchmarkList, sPointBenchmarkList) -- run all examples
      ([], categories) -> (benchmarksByCategory categories, sPointBenchmarksByCategory categories)
      (files, _) -> undefined
  doModes <- return ["graded", "ungraded"]

  let relevantModes = lookupMany doModes modes

  -- Collect the results
  resultsPerMode <-
    forM relevantModes $ \(modeTitle, mode) -> do

      let items' = if mode == "ungraded" then snd items else fst items
      forM (filter (\(_, _, path) -> ".gr" `isSuffixOf` path) items') $ \(texName, category, file) -> do
          -- Run granule
          results <- measureSynthesis repeatTimes file mode logIdent
          return (texName, category, file, mode, results)


      -- Paper view
      -- Transpose the results to get per-file rather than per-mode
  -- putStrLn $ "results per mode: " <> (show resultsPerMode)
  let splitTimeAndSMT = True
  let resultsPerFile = transpose resultsPerMode


  res <- foldM (\seq@(resultsFormattedPrev, prevCategory) resultsPerModePerFile -> do 
          let category = show $ snd5 $ head resultsPerModePerFile
          let texName =  show $ fst5 $ head resultsPerModePerFile
          let categoryMessage = if fromMaybe "" prevCategory /= category 
                                then "\\hline \\multirow{5}{*}{{\\rotatebox{90}{\\textbf{" <> (show category) <> "}}}}"
                                else ""
          putStr categoryMessage        
          putStrLn " & "

          putStr $ texName <> " & "
          leadTime <- foldM (\(lead :: Maybe (String, Double) ) (texName, category, fileName, mode, results@(meausurements, aggregate)) -> do
            let currentTime = read $ report1String results synthTime
            case lead of 
              Nothing -> return $ Just (mode, currentTime)
              Just (_, leadTime) -> 
                if (not $ timeout aggregate) && leadTime > currentTime then 
                  return $ Just (mode, currentTime)
                else
                  return lead
            ) Nothing resultsPerModePerFile

          resultsFormatted <- forM resultsPerModePerFile $ (\(texName, category, fileName, mode, results@(measurements, aggregate)) -> do
            return $  sequence (intersperse (putStr " & ") (
              if splitTimeAndSMT then
                if timeout aggregate then
                  [ putStr "\\fail{}",  putStr "Timeout", putStr "-" ]
                else
                  [ report1 results success
                  , if fromMaybeFst "" leadTime == mode then reportLead results synthTime else report results synthTime
                  , report1 results smtCalls
                  , report1 results pathsExplored ]
              else
                [ report1 results success
                , report results synthTime
                , report results solverTime
                , report1 results smtCalls
                , report1 results meanTheoremSize
                , report1 results pathsExplored] )))

          forM_ resultsFormatted $ \res -> do res
          putStrLn "\\\\ \n%"
          return (resultsFormatted:resultsFormattedPrev, Just category)
          ) ([], Nothing) resultsPerFile
  putStrLn "\\\\ \n%"

fst5 (x, _, _, _, _) = x
snd5 (_, x, _, _, _) = x

fromMaybeFst x Nothing  = x
fromMaybeFst _ (Just (x, _)) = x

fromMaybeSnd x Nothing  = x
fromMaybeSnd _ (Just (_, x)) = x

pad str = str ++ (replicate (if length str > 25 then 0 else 25 - length str) ' ')

lookupMany xs map = mapMaybe (flip lookup map) xs

measureSynthesis :: Int -> String -> FilePath -> String -> IO ([Measurement], Measurement)
measureSynthesis repeatTimes file mode logIdent = do
    measurements <- replicateM repeatTimes measure
    return (measurements, aggregate measurements)
 where
   -- Command to run granule
   cmd   = "gr " <> file <> " " <> flags <> " >> " <> "log-" <> logIdent
   flags = unwords ["--synthesis","--benchmark","--raw-data","--ignore-holes",mode]

   -- Measurement computation
   measure :: IO Measurement
   measure = do
     code <- system $ cmd
     case code of
       ExitFailure _ -> do
         return $ Measurement
           { smtCalls = 0
           , synthTime = 0.00
           , proverTime = 0.00
           , solverTime = 0.00
           , meanTheoremSize = 0.00
           , success = False
           , timeout = True
           , pathsExplored = 0}
       ExitSuccess -> do
         logData <- SIO.readFile $ "log-" <> logIdent
         -- Read off the current results which should be on the second last line of the log file
         let k = length (lines logData)
        --  putStrLn $ show $ lines logData
        --  putStrLn "STOP"
        --  putStrLn $ show $ (head $ drop (k - 1) $ lines logData)
        --  putStrLn "BLAH"
       
         return $ read (head $ drop (k - 1) $ lines logData)

-- Aggregate the results from multiple runs
aggregate :: [Measurement] -> Measurement
aggregate results =
  let n = fromIntegral $ length results
  in Measurement
      { smtCalls = the (map smtCalls results)
      , synthTime  = sum (map synthTime results) / n
      , proverTime = sum (map proverTime results) / n
      , solverTime = sum (map solverTime results) / n
      , meanTheoremSize = the (map meanTheoremSize results)
      , success = the (map success results)
      , timeout = the (map timeout results)
      , pathsExplored = the (map pathsExplored results)
      }

