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

-- | Extract \begin{granule} code blocks \end{granule} from tex files on a
-- line-by-line basis. Maps other lines to the empty string, such that line
-- numbers are preserved.
unLatex :: String -> String
unLatex = processGranuleLatex id (const "")

-- | Transform the input by the given processing functions for Granule and
-- Latex (currently operating on a line-by-line basis)
processGranuleLatex
  :: (String -> String) -- the processing function to apply to each line of granule code
  -> (String -> String) -- the processing function to apply to each line of latex
  -> (String -> String)
processGranuleLatex fGr fTex = lines >>> (`zip` [1..]) >>> go Latex >>> unlines
  where
    go :: DocType -> [(String, Int)] -> [String]
    go Latex ((line, lineNumber) : ls)
      | strip line == "\\begin{granule}" = fTex line : go GranuleBlock ls
      | strip line == "\\end{granule}"   = error $ "Unmatched `\\end{granule}` on line " <> show lineNumber
      | otherwise                        = fTex line : go Latex ls
    go GranuleBlock ((line, lineNumber) : ls)
      | strip line == "\\end{granule}"   = fTex line : go Latex ls
      | strip line == "\\begin{granule}" = error $ "Unmatched `\\begin{granule}` on line " <> show lineNumber
      | otherwise                        = fGr line : go GranuleBlock ls
    go _ []                              = []

    -- Remove trailing whitespace (hey, should we be using @Text@?)
    strip :: String -> String
    strip = reverse . dropWhile isSpace . reverse . dropWhile isSpace
