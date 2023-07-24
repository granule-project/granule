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
   , programSize     :: Integer
   , contextSize     :: Integer
   , examplesUsed    :: Integer
   , cartesian       :: Bool
   , cartAttempts    :: Integer
    -- To extend with other info...
   }
   deriving (Read, Show)

class Report a where
  report :: ([Measurement], Measurement) -> (Measurement -> a) -> IO ()
  report1 :: ([Measurement], Measurement) -> (Measurement -> a) -> IO ()
  reportLead :: ([Measurement], Measurement) -> (Measurement -> a) -> IO ()
  reportLead2 :: ([Measurement], Measurement) -> (Measurement -> a) -> IO ()
  reportString :: ([Measurement], Measurement) -> (Measurement -> a) -> String
  report1String :: ([Measurement], Measurement) -> (Measurement -> a) -> String


instance Report Bool where
  report (_, aggregate) view | view aggregate = putStr "\\success{}"
                             | otherwise      = putStr "\\fail{} "
  report1 = report
  reportLead = report
  reportLead2 = report

  reportString (_, aggregate) view | view aggregate = "\\success{}"
                                   | otherwise      = "\\fail{} "
  report1String = reportString

instance Report Integer where
  report (_, aggregate) view =
    printf "%3d      " (view aggregate)
  report1 = report
  reportLead = report
  reportLead2 = report
  reportString (_, aggregate) view =
    printf "%3d      " (view aggregate)
  report1String = reportString

instance Report Double where
  report (results, aggregate) view =
    printf "%6.2f (\\stderr{%6.2f})" (view aggregate) (stdError $ map view results)
  reportLead (results, aggregate) view =
    printf "{\\highlight{$ %6.2f (\\stderr{%6.2f}) $}}" (view aggregate) (stdError $ map view results)
  reportLead2 (results, aggregate) view =
    printf "{\\newhighlight{$ %6.2f (\\stderr{%6.2f}) $}}" (view aggregate) (stdError $ map view results)
  report1 (_, aggregate) view =
    printf "%6.2f" (view aggregate)
  reportString (results, aggregate) view =
    printf "%6.2f (\\stderr{%6.2f})" (view aggregate) (stdError $ map view results)
  report1String (_, aggregate) view =
    printf "%6.2f" (view aggregate)

modes :: [(String, (String, String))]
modes = [
      ("Graded", ("Graded", ""))
    , ("Cartesian", ("Cartesian", "--cart-synth 1"))
    , ("Cartesian (No Retries)", ("Cartesian (No Retries)", "--cart-synth 2"))
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

attemptsToSeconds :: Integer -> Double
attemptsToSeconds n = 1000.0 * fromIntegral n

main :: IO ()
main = do
  argsMain <- getArgs
  hFlush stdout
  -- Get current time for log file name
  currentTime <- T.getCurrentTime
  let logIdent = T.formatTime T.defaultTimeLocale "%F-%H-%M" currentTime

  (files, categories, fpm, repeatTimes) <- return $ processArgs argsMain

  let items = benchmarksToRun benchmarkList
  let doModes = ["Graded", "Cartesian", "Cartesian (No Retries)"]
  let fpm = True
  let repeatTime = defaultRepeatTrys

  let relevantModes = lookupMany doModes modes

  -- Collect the results
  resultsPerMode <-
    forM relevantModes $ \(modeTitle, mode) -> do

      forM (filter (\(_, _, path, _) -> ".gr" `isSuffixOf` path) items) $ \(texName, category, file, _) -> do
          -- Run granule
          results <- measureSynthesis repeatTimes file mode logIdent
          return (texName, category, file, mode, results)

      -- Paper view
      -- Transpose the results to get per-file rather than per-mode
  -- putStrLn $ "results per mode: " <> (show resultsPerMode)
  let splitTimeAndSMT = True
  let resultsPerFile = transpose resultsPerMode

  putStrLn "\\begin{table}[t]"
  putStrLn "{\\footnotesize{"
  putStrLn "\\begin{center}"
  putStrLn "\\setlength{\\tabcolsep}{0.3em}"
  -- let seps = replicate (length relevantModes) "p{0.75em}rccc"
  putStrLn $ "\\begin{tabular}{p{1.25em}cc|p{0.75em}rc|p{0.75em}rcc|p{0.75em}rc} & & & "
  putStrLn $ "\\multicolumn{3}{c|}{Graded}&\\multicolumn{4}{c|}{Cartesian}&\\multicolumn{3}{c|}{Cartesian (No Retries)} \\\\ \\hline \\multicolumn{2}{c}{{Problem}}& \\multicolumn{1}{c|}{{Ctxt}} & & \\multicolumn{1}{c}{$\\mu{T}$ (ms)} & \\multicolumn{1}{c|}{{\\#/Exs.}} & & \\multicolumn{1}{c}{$\\mu{T}$ (ms)} & \\multicolumn{1}{c}{\\textsc{N}} & \\multicolumn{1}{c|}{$\\mu{T}$ + OracleT (ms)}  & & \\multicolumn{1}{c}{$\\mu{T}$ (ms)} & \\multicolumn{1}{c|}{{\\#/Exs.}}\\\\ \\hline"
  -- let colHeadings = map (\(modeTitle, _) -> "\\multicolumn{5}{c|}{"<> modeTitle <> "}") relevantModes
  -- putStrLn $ intercalate "&" colHeadings <> "\\\\ \\hline"

  -- let subHeadings = replicate (length relevantModes) "\\multicolumn{1}{c}{$\\mu{T}$ (ms)} & \\multicolumn{1}{c}{\\textsc{SMT}} & \\multicolumn{1}{c}{Paths} & \\multicolumn{1}{r|}{\\textsc{N}}"
  -- putStrLn $ "\\multicolumn{2}{r}{{Problem}}& \\multicolumn{1}{c|}{{Exs}} & & " <> intercalate " & & " subHeadings <> "\\\\ \\hline"

  res <- foldM (\seq@(resultsFormattedPrev, prevCategory) resultsPerModePerFile -> do
          let category = snd5 $ head resultsPerModePerFile
          let texName = fst5 $ head resultsPerModePerFile
          let categoryMessage = if fromMaybe "" prevCategory /= category
                                then "\\hline \\multirow{" <> show (categorySize category True) <> "}{*}{{\\rotatebox{90}{\\textbf{" <> category <> "}}}}"
                                else ""

          putStr categoryMessage
          putStrLn " & "
          putStr texName 
          putStr " & "
          let ctxt = fifth5 $ head resultsPerModePerFile
          report1 ctxt contextSize

          leadTime <- foldM (\(lead :: (Maybe (String, Double), Bool) ) (texName, category, fileName, mode, results@(meausurements, aggregate)) -> do
            let currentTime = read $ report1String results synthTime
            case lead of
              (Nothing, _) -> return (Just (mode, currentTime), False)
              (Just (m, leadTime), cartLead) ->
                if not (timeout aggregate) && leadTime > currentTime then
                  if mode == "--cart-synth 1" then
                    if leadTime > currentTime +  attemptsToSeconds (cartAttempts aggregate) then
                      return $ (Just (mode, currentTime), cartLead)
                    else
                      return (Just (m, leadTime), True)
                  else
                    return $ (Just (mode, currentTime), cartLead)
                else
                  return lead
            ) (Nothing, False) resultsPerModePerFile

          resultsFormatted <- forM resultsPerModePerFile $ (\(texName, category, fileName, mode, results@(measurements, aggregate)) -> do
            return $  sequence (if splitTimeAndSMT then
                if not $ success aggregate then
                  [
                      putStr " & "
                      , putStr "\\fail{}"
                      , putStr " & "
                      ,  putStr "Timeout"
                      , putStr " & "
                      , putStr "-"
                      , if mode == "--cart-synth 1" then putStr " & " else putStr ""
                      , if mode == "--cart-synth 1" then putStr "-"  else putStr ""
                      ]
                else
                  [ putStr " & ", report1 results success
                  , putStr " & "
                  , 
                    if mode == "--cart-synth 1" then 
                      if not $ snd leadTime then 
                        if fromMaybeFst "" (fst leadTime) == mode then reportLead results synthTime else report results synthTime
                      else 
                        reportLead2 results synthTime
                    else 
                      if fromMaybeFst "" (fst leadTime) == mode then reportLead results synthTime else report results synthTime
                  , putStr " & "
                  , if mode == "--cart-synth 1" then 
                      report1 results cartAttempts
                    else  
                      report1 results examplesUsed

                  , if mode == "--cart-synth 1" then putStr " & " else putStr ""
                  , if mode == "--cart-synth 1" then do
                        printf  "%6.2f" (synthTime aggregate + attemptsToSeconds (cartAttempts aggregate))  else putStr ""
                  ]
              else
                [ report1 results success
                , report results synthTime
                , report results solverTime
                , report1 results smtCalls
                , report1 results meanTheoremSize
                , report1 results pathsExplored]))

          forM_ resultsFormatted $ \res -> do res
          putStrLn "\\\\ \n%"
          return (resultsFormatted:resultsFormattedPrev, Just category)
          ) ([], Nothing) resultsPerFile



  putStrLn "\\end{tabular}"
  putStrLn "\\end{center}}}"
  putStrLn "\\caption{Results. $\\mu{T}$ in \\emph{ms} to 2 d.p. with standard sample error in brackets}"
  putStrLn "\\label{tab:results}"
  putStrLn "\\vspace{-2.5em}"
  putStrLn "\\end{table}"
  -- removeFile $ "log-" <> logIdent


fst5 (x, _, _, _, _) = x
fifth5 (_, _, _, _, x) = x
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
           , pathsExplored = 0
           , programSize = 0
           , contextSize = 0
           , examplesUsed = 0
           , cartesian = False
           , cartAttempts = 0 }
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
      { smtCalls = fromMaybe 0 $ the' (map smtCalls results)
      , synthTime  = sum (map synthTime results) / n
      , proverTime = sum (map proverTime results) / n
      , solverTime = sum (map solverTime results) / n
      , meanTheoremSize = fromMaybe 0 $ the' (map meanTheoremSize results)
      , success = fromMaybe False $ the' (map success results)
      , timeout = fromMaybe True $ the' (map timeout results)
      , pathsExplored = fromMaybe 0 $ the' (map pathsExplored results)
      , programSize = fromMaybe 0 $ the' (map programSize results)
      , contextSize = fromMaybe 0 $ the' (map contextSize results)
      , examplesUsed = fromMaybe 0 $ the' (map examplesUsed results)
      , cartesian = fromMaybe False $ the' (map cartesian results)
      , cartAttempts = fromMaybe 0 $ the' (map cartAttempts results)
      }


the' :: Eq a => [a] -> Maybe a
the' (x:xs)
  | all (x ==) xs = Just x
  | otherwise      = Nothing
the' []            = Nothing