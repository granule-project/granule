module Language.Granule.Syntax.Preprocessor.Latex (unLatex) where

import Data.Char (isSpace)
import Control.Arrow ((>>>))

data DocType
  = Latex
  | GranuleCodeBlock

-- | Extract fenced code blocks labeled  "granule" from Latex files on a
-- line-by-line basis. Maps other lines to the empty string, such that line
-- numbers are preserved.
unLatex :: String -> String
unLatex = lines >>> map strip >>> go Latex >>> unlines
  where
    go :: DocType -> [String] -> [String]
    go Latex ("\\begin{granule}"          : xs) = "" : go GranuleCodeBlock xs
    go Latex (_                           : xs) = "" : go Latex xs
    go GranuleCodeBlock ("\\end{granule}" : xs) = "" : go Latex xs
    go GranuleCodeBlock (x                : xs) = x  : go GranuleCodeBlock xs
    go _ []                                     = []

-- | Remove trailing whitespace (hey, should we be using @Text@?)
strip :: String -> String
strip = reverse . dropWhile isSpace . reverse . dropWhile isSpace
