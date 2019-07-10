module Language.Granule.Syntax.Preprocessor.Latex
  ( processGranuleLatex
  , unLatex
  )
  where

import Data.Char (isSpace)
import Control.Arrow ((>>>))

data DocType
  = Latex
  | GranuleBlock

-- | Extract @\begin{env}@ code blocks @\end{env}@ from tex files on a
-- line-by-line basis, where @env@ is the name of the relevant environment. Maps
-- other lines to the empty string, such that line numbers are preserved.
unLatex :: String -> (String -> String)
unLatex env = processGranuleLatex (const "") env id

-- | Transform the input by the given processing functions for Granule and Latex
-- (currently operating on a line-by-line basis)
processGranuleLatex
  :: (String -> String) -- ^ the processing function to apply to each line of latex
  -> String             -- ^ the name of the environment to check
  -> (String -> String) -- ^ the processing function to apply to each line of granule code
  -> (String -> String)
processGranuleLatex fTex env fGr = lines >>> (`zip` [1..]) >>> go Latex >>> unlines
  where
    go :: DocType -> [(String, Int)] -> [String]
    go Latex ((line, lineNumber) : ls)
      | strip line == "\\begin{" <> env <> "}" = fTex line : go GranuleBlock ls
      | strip line == "\\end{" <> env <> "}"   = error $ "Unmatched `\\end{" <> env <> "}` on line " <> show lineNumber
      | otherwise                        = fTex line : go Latex ls
    go GranuleBlock ((line, lineNumber) : ls)
      | strip line == "\\end{" <> env <> "}"   = fTex line : go Latex ls
      | strip line == "\\begin{" <> env <> "}" = error $ "Unmatched `\\begin{" <> env <> "}` on line " <> show lineNumber
      | otherwise                        = fGr line : go GranuleBlock ls
    go _ []                              = []

    -- Remove trailing whitespace (hey, should we be using @Text@?)
    strip :: String -> String
    strip = reverse . dropWhile isSpace . reverse . dropWhile isSpace
