{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Granule.Benchmarks where

import Data.Csv

import GHC.Generics
import System.IO
import System.Exit (exitFailure)
import qualified Data.ByteString.Lazy as LB
import Data.Vector (toList)

import Data.Char (isSpace)
import Data.List (nub)

import Paths_granule_benchmark ( getDataDir )

trim :: String -> String
trim = f . f
   where f = reverse . dropWhile isSpace

rootDir :: String
rootDir = ""

getBenchmarkFile :: IO FilePath
getBenchmarkFile = do
    dataDir <- getDataDir
    pure $ dataDir<>"/benchmarkList"

benchmarkList :: IO [(String, String, String, Bool)]
benchmarkList = do
    benchmarkFile <- getBenchmarkFile
    csv <- LB.readFile benchmarkFile
    case decode NoHeader csv of
        (Left _) -> error "Couldn't parse benchmark list - bad data"
        (Right res) -> do
            let resList = map (\(a, b, c, d) -> (trim a, trim b, trim c, read d)) $ toList res 
            return resList

inFiles :: [(String, String)] -> String -> String -> Bool
inFiles [] _ _ = False
inFiles ((ftitle, fcat):files) file cat = if file == ftitle && cat == fcat then True else inFiles files file cat 

benchmarkListFullPath :: [(String, String, String, Bool)] -> [(String, String, String, Bool)]
benchmarkListFullPath = map (\(title, cat, path, incl) -> (title, cat, rootDir <> path, incl))


benchmarksToRun :: (Maybe [String]) -> (Maybe [(String, String)]) -> [(String, String, String, Bool)] -> [(String, String, String, Bool)]
benchmarksToRun (Just cats) (Just files) bList = nub $ benchmarkListFullPath (filter (\(_,_,_,b) -> b) (benchmarksByCategory bList cats True)) ++ (filter (\(title,cat,_,_) -> inFiles files title cat) bList)
benchmarksToRun Nothing (Just files) bList = benchmarkListFullPath (filter (\(title,cat,_,_) -> inFiles files title cat) bList)
benchmarksToRun (Just cats) Nothing bList = benchmarkListFullPath (filter (\(_,_,_,b) -> b) (benchmarksByCategory bList cats True))
benchmarksToRun Nothing Nothing bList = benchmarkListFullPath (filter (\(_,_,_,b) -> b) bList)

benchmarksByCategory :: [(String, String, String, Bool)] -> [String] -> Bool -> [(String, String, String, Bool)]
benchmarksByCategory bList bs onlyIncls = foldr
      (\ c
         -> (++)
              (filter
                 (\ (_, c', _, incl) -> c' == c && (incl || not onlyIncls))
                 (benchmarkListFullPath bList)))
      []
      bs 

categorySize :: [(String, String, String, Bool)] -> String -> Bool -> Int
categorySize bList cat onlyIncls = length $ benchmarksByCategory bList [cat] onlyIncls





