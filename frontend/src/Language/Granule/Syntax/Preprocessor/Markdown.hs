module Language.Granule.Syntax.Preprocessor.Markdown (unmarkdown) where

import Data.Char (isSpace)
import Control.Arrow ((>>>))

data DocType
  = Markdown
  | GranuleCodeBlockTwiddle
  | GranuleCodeBlockTick

-- | Extract fenced code blocks labeled  "granule" from markdown files on a
-- line-by-line basis. Maps other lines to the empty string, such that line
-- numbers are preserved.
unmarkdown :: String -> String
unmarkdown = lines >>> map stripEnd >>> go Markdown >>> unlines
  where
    go :: DocType -> [String] -> [String]
    go Markdown ("~~~granule"         : xs) = "" : go GranuleCodeBlockTwiddle xs
    go Markdown ("~~~ granule"        : xs) = "" : go GranuleCodeBlockTwiddle xs
    go Markdown ("```granule"         : xs) = "" : go GranuleCodeBlockTick xs
    go Markdown ("``` granule"        : xs) = "" : go GranuleCodeBlockTick xs
    go Markdown (_                    : xs) = "" : go Markdown xs
    go GranuleCodeBlockTwiddle ("~~~" : xs) = "" : go Markdown xs
    go GranuleCodeBlockTwiddle (x     : xs) = x  : go GranuleCodeBlockTwiddle xs
    go GranuleCodeBlockTick ("```"    : xs) = "" : go Markdown xs
    go GranuleCodeBlockTick (x        : xs) = x  : go GranuleCodeBlockTick xs
    go _ []                                 = []

-- | Remove trailing whitespace (hey, should we be using @Text@?)
stripEnd :: String -> String
stripEnd = reverse . dropWhile isSpace . reverse
