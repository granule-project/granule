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
   , checkTime       :: Double
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
  reportLeadString :: ([Measurement], Measurement) -> (Measurement -> a) -> String
  reportLead2String :: ([Measurement], Measurement) -> (Measurement -> a) -> String


instance Report Bool where
  report (_, aggregate) view | view aggregate = putStr "\\success{}"
                             | otherwise      = putStr "\\fail{} "
  report1 = report
  reportLead = report
  reportLead2 = report

  reportString (_, aggregate) view | view aggregate = "\\success{}"
                                   | otherwise      = "\\fail{} "
  report1String = reportString
  reportLeadString = reportString
  reportLead2String = reportString

instance Report Integer where
  report (_, aggregate) view =
    printf "%3d      " (view aggregate)
  report1 = report
  reportLead (_, aggregate) view =
    printf "{\\newhighlight{$ %3d $}}" (view aggregate)
  reportLead2 = report
  reportString (_, aggregate) view =
    printf "%3d      " (view aggregate)
  report1String (_, aggregate) view =
    printf "%3d      " (view aggregate)
  reportLeadString (_, aggregate) view =
    printf "{\\newhighlight{$ %3d $}}" (view aggregate)
  reportLead2String = reportLeadString

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
  reportLeadString (results, aggregate) view =
    printf "{\\highlight{$ %6.2f (\\stderr{%6.2f}) $}}" (view aggregate) (stdError $ map view results)
  reportLead2String (results, aggregate) view =
    printf "{\\highlight{$ %6.2f (\\stderr{%6.2f}) $}}" (view aggregate) (stdError $ map view results)


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

latexfile :: FilePath
latexfile = "benchmarkTable"

main :: IO ()
main = do
  argsMain <- getArgs
  hFlush stdout
  -- Get current time for log file name
  currentTime <- T.getCurrentTime
  let logIdent = T.formatTime T.defaultTimeLocale "%F-%H-%M" currentTime

  (files, categories, fpm, repeatTimes) <- return $ processArgs argsMain

  let items = benchmarksToRun benchmarkList
  let doModes = ["Graded", "Cartesian"]
  let fpm = True
  let repeatTime = defaultRepeatTrys

  let relevantModes = lookupMany doModes modes
  putStrLn "Running benchmarks..."
  -- putStrLn $ "No. of retries: " <> show defaultRepeatTrys

  -- Collect the results
  resultsPerMode <-
    forM relevantModes $ \(modeTitle, mode) -> do
      putStrLn $ "---------------------------"
      putStrLn $ "Running benchmarks for mode: " <> modeTitle

      forM (filter (\(_, _, path, _) -> ".gr" `isSuffixOf` path) items) $ \(texName, category, file, _) -> do
          -- Run granule
          putStrLn $ "   Running benchmark: " <> texName
          results <- measureSynthesis repeatTimes file mode logIdent
          return (texName, category, file, mode, results)

  -- Transpose the results to get per-file rather than per-mode
  let splitTimeAndSMT = True
  let resultsPerFile = transpose resultsPerMode
  putStrLn $ "---------------------------"
  putStrLn "Benchmarks complete. Creating table of results..."

  let tableOuter = latexContentHeader

  tableContent <- foldM (\(table, prevCategory) resultsPerModePerFile -> do
          let category = snd5 $ head resultsPerModePerFile
          let texName = fst5 $ head resultsPerModePerFile
          let categoryMessage = if fromMaybe "" prevCategory /= category
                                then "\\hline \\multirow{" <> show (categorySize category True) <> "}{*}{{\\rotatebox{90}{\\textbf{" <> category <> "}}}}"
                                else ""

          let ctxt = fifth5 $ head resultsPerModePerFile
          let cartCtxt = fifth5 $ last resultsPerModePerFile
          let examples :: Integer = read $ report1String ctxt examplesUsed
          let cartExamples :: Integer = read $ report1String cartCtxt examplesUsed
          let ctxtSize :: Integer = read $ report1String ctxt contextSize
          let cartExamplesDiff = cartExamples - examples

          let (table' :: String) = table <> categoryMessage <> " & " <> texName <> " & " <> show ctxtSize <> " & " <> show examples
          let table'' = if cartExamplesDiff > 0 then table' <> " (+" <> show cartExamples <> ")" else table'

          leadTime <- foldM (\(lead :: (Maybe (String, Double), Bool) ) (texName, category, fileName, mode, results@(meausurements, aggregate)) -> do
            let currentTime = if mode == "--cart-synth 1" then read $ report1String results checkTime else read $ report1String results synthTime
            case lead of
              (Nothing, _) -> return (Just (mode, currentTime), False)
              (Just (m, leadTime), cartLead) ->
                if not (timeout aggregate) && leadTime > currentTime then
                  if mode == "--cart-synth 1" then
                      return $ (Just (mode, currentTime), True)
                    -- if leadTime > currentTime +  attemptsToSeconds (cartAttempts aggregate) then
                    --   return $ (Just (mode, currentTime), cartLead)
                    -- else
                    --   return (Just (m, leadTime), True)
                  else
                    return $ (Just (mode, currentTime), cartLead)
                else
                  return lead
            ) (Nothing, False) resultsPerModePerFile

          fewestPaths <- foldM (\(shortest :: Maybe (String, Int)) (texName, category, fileName, mode, results@(measurements, aggregate)) -> do
            let currentPaths = read $ report1String results pathsExplored
            case shortest of
              Nothing -> return $ Just (mode, currentPaths)
              (Just (m, shortestPaths)) ->
                if not (timeout aggregate) && shortestPaths > currentPaths then
                  return $ Just (mode, currentPaths)
                else
                  if not (timeout aggregate) && shortestPaths == currentPaths then
                  return Nothing
                  else return shortest
              ) Nothing resultsPerModePerFile

          tableFormatted <- foldM (\tableI (texName, category, fileName, mode, results@(measurements, aggregate)) -> do
            if not $ success aggregate || timeout aggregate then
              return $ tableI <> " & \\fail {} & Timeout & " <> (if mode == "--cart-synth 1" then "- & " else "")
            else do
              let tableI1 = tableI <> " & \\success{} & "
              let checkSynthTime
                    | mode == "--cart-synth 1" = if snd leadTime then reportLeadString results checkTime
                        -- if fromMaybeFst "-" (fst leadTime) == mode then reportLeadString results checkTime else reportString results checkTime
                      else
                        reportString results checkTime
                    | fromMaybeFst "-" (fst leadTime) == mode = reportLeadString results synthTime
                    | otherwise = reportString results synthTime

              let tableI2 = tableI1 <> checkSynthTime <> " & "
              let pathsCartAttempts
                    | mode == "--cart-synth 1" = report1String results cartAttempts
                    | fromMaybeFst "-" fewestPaths == mode = do
                            reportLeadString results pathsExplored
                    | otherwise = do
                            reportString results pathsExplored
              let tableI3 = tableI2 <> pathsCartAttempts
              let cartPaths = (if fromMaybeFst "-" fewestPaths == mode then reportLeadString results pathsExplored else reportString results pathsExplored)

              let tableI4 = if mode == "--cart-synth 1" then tableI3 <> " & " <> cartPaths else tableI3
              return tableI4) "" resultsPerModePerFile

          let tableOut = table'' <> tableFormatted <> "\\\\ \n"
          return (tableOut, Just category)
          ) (tableOuter, Nothing) resultsPerFile



  let tableDone = (fst tableContent) <> latexContentFooter
  writeFile (latexfile <> ".tex") tableDone
  putStrLn $ "LaTeX table created. Written to: " <> latexfile <> ".tex"
  putStrLn $ "Generating PDF... "
  code <- system $ "pdflatex -shell-escape -synctex=1 -file-line-error -interaction=nonstopmode -halt-on-error " <> latexfile <> ".tex > /dev/null" 
  case code of 
    ExitFailure _ -> do
      putStrLn $ "Unable to generate PDF from " <> latexfile <> ".tex!"
    ExitSuccess -> do 
      putStrLn $ "Done! The benchmark results table can be viewed in: " <> latexfile <> ".pdf"
  
  -- removeFile $ "log-" <> logIdent
  -- putStrLn tableDone


fst5 (x, _, _, _, _) = x
fifth5 (_, _, _, _, x) = x
snd5 (_, x, _, _, _) = x

fromMaybeFst x Nothing  = x
fromMaybeFst _ (Just (x, _)) = x

fromMaybeSnd x Nothing  = x
fromMaybeSnd _ (Just (_, x)) = x

pad str = str ++ (replicate (if length str > 25 then 0 else 25 - length str) ' ')

lookupMany xs map = mapMaybe (flip lookup map) xs

measureSynthesis :: Int -> FilePath -> String -> FilePath -> IO ([Measurement], Measurement)
measureSynthesis repeatTimes file mode logIdent = do
    measurements <- replicateM' 1 repeatTimes
    removeFile $ "log-" <>  logIdent
    return (measurements, aggregate measurements)
 where
   -- Command to run granule
   cmd   = "gr " <> file <> " " <> flags <> " >> " <> "log-" <> logIdent
   flags = unwords ["--synthesis","--benchmark","--raw-data","--ignore-holes",mode]
   replicateM' curr no | no == curr = do
    res <- measure curr no
    return [res]
   replicateM' curr no = do
      res <- measure curr no
      reses <- replicateM' (curr+1) no
      return $ res : reses -- replicateM' (curr+1) no
      -- return $ res : reses

   -- Measurement computation
   measure :: Int -> Int -> IO Measurement
   measure no total = do
     putStrLn $ "     Repeat no: [" <> show no <> "/" <> show total <> "]"
     code <- system $ cmd
     case code of
       ExitFailure _ -> do
         return $ Measurement
           { smtCalls = 0
           , synthTime = 0.00
           , proverTime = 0.00
           , solverTime = 0.00
           , meanTheoremSize = 0.00
           , checkTime = 0.00
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
      , checkTime = sum (map checkTime results) / n
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


latexContentHeader :: String
latexContentHeader =
     "\\documentclass{article}\n"
  <> "\\usepackage{mathpartir}\n"
  <> "\\usepackage{amsmath}\n"
  <> "\\usepackage{amsfonts}\n"
  <> "\\usepackage[dvipsnames]{xcolor}\n"
  <> "\\usepackage{xypic}\n"
  <> "\\usepackage{float}\n"
  <> "\\usepackage{multirow}\n"
  <> "\\usepackage{resizegather}\n"
  <> "\\definecolor{mypink3}{cmyk}{0, 0.82, 0.98, 0.28}\n"
  <> "\\newcommand{\\stderr}[1]{\\textcolor{gray}{${#1}$}}\n"
  <> "\\newcommand{\\fail}{\\textcolor{mypink3}{$\\times$}}\n"
  <> "\\newcommand{\\success}{\\checkmark}\n"
  <> "\\newcommand{\\highlight}[1]{%\n"
  <> "{\\setlength{\\fboxsep}{0pt}\\colorbox{SkyBlue!50}{$\\displaystyle#1$}}}\n"
  <> "\\newcommand{\\newhighlight}[1]{%\n"
  <> "{\\setlength{\\fboxsep}{0pt}\\colorbox{yellow!50}{$\\displaystyle#1$}}}\n"
  <> "\\begin{document}\n"
  <> "\\begin{table}[t]\n"
  <> "{\\footnotesize{\n"
  <> "\\begin{center}\n"
  <> "\\setlength{\\tabcolsep}{0.3em}\n"
  <> "\\begin{tabular}{p{1.25em}ccl|p{0.75em}rc|p{0.75em}rcc} & & & & \n"
  <> "\\multicolumn{3}{c|}{Graded}&\\multicolumn{4}{c|}{Cartesian + Graded type-check} \\\\ \\hline \\multicolumn{2}{c}{{Problem}}& \\multicolumn{1}{c}{{Ctxt}} & \\multicolumn{1}{c|}{{\\#/Exs.}} & & \\multicolumn{1}{c}{$\\mu{T}$ (ms)} & \\multicolumn{1}{c|}{{Paths}} & & \\multicolumn{1}{c}{$\\mu{T}$ (ms)} & \\multicolumn{1}{c}{\\textsc{N}} & \\multicolumn{1}{c|}{{Paths}} \\\\ \\hline\n"



latexContentFooter :: String
latexContentFooter =
     "\n\\end{tabular}\n"
  <> "\\end{center}}}\n"
  <> "\\caption{Results. $\\mu{T}$ in \\emph{ms} to 2 d.p. with standard sample error in brackets}\n"
  <> "\\label{tab:results}\n"
  <> "\\vspace{-2.5em}\n"
  <> "\\end{table}\n"
  <> "\\end{document}"

