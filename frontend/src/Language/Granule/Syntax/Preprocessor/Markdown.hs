module Language.Granule.Syntax.Preprocessor.Markdown
  ( processGranuleMarkdown
  , unMarkdown
  )
  where

import Data.Char (isSpace)
import Control.Arrow ((>>>))

data DocType
  = Markdown
  | GranuleBlockTwiddle
  | GranuleBlockTick

-- | Extract fenced code blocks labeled  "granule" from markdown files on a
-- line-by-line basis. Maps other lines to the empty string, such that line
-- numbers are preserved.
unMarkdown :: String -> String
unMarkdown = processGranuleMarkdown id (const "")

-- | Transform the input by the given processing functions for Granule and
-- Markdown (currently operating on a line-by-line basis)
processGranuleMarkdown
  :: (String -> String) -- the processing function to apply to each line of granule code
  -> (String -> String) -- the processing function to apply to each line of markdown
  -> (String -> String)
processGranuleMarkdown fGr fMd = lines >>> (`zip` [1..]) >>> go Markdown >>> unlines
  where
    go :: DocType -> [(String, Int)] -> [String]
    go Markdown ((line, lineNumber) : ls)
      | strip line == "~~~granule" || strip line == "~~~ granule"
        = fMd line : go GranuleBlockTwiddle ls
      | strip line == "```granule" || strip line == "``` granule"
        = fMd line : go GranuleBlockTick ls
      | otherwise
        = fMd line : go Markdown ls
    go GranuleBlockTwiddle ((line, lineNumber) : ls)
      | strip line == "~~~"
        = fMd line : go Markdown ls
      | strip line == "~~~granule"
        || strip line == "~~~ granule"
        || strip line == "```granule"
        || strip line == "``` granule"
          = error
            $ "Unexpected `"
            <> line
            <> "` on line "
            <> show lineNumber
            <> " while inside a granule code block (~~~)"
      | otherwise
        = fGr line : go GranuleBlockTwiddle ls
    go GranuleBlockTick ((line, lineNumber) : ls)
      | strip line == "```"
        = fMd line : go Markdown ls
      | strip line == "~~~granule"
        || strip line == "~~~ granule"
        || strip line == "```granule"
        || strip line == "``` granule"
          = error
            $ "Unexpected `"
            <> line
            <> "` on line "
            <> show lineNumber
            <> " while inside a granule code block (```)"
      | otherwise
        = fGr line : go GranuleBlockTick ls
    go _ [] = []

    -- Remove trailing whitespace (hey, should we be using @Text@?)
    strip :: String -> String
    strip = reverse . dropWhile isSpace . reverse . dropWhile isSpace
