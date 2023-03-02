module Language.Granule.Syntax.Preprocessor.Markdown
  ( processGranuleMarkdown
  , unMarkdown
  )
  where

import Data.Char (isSpace)
import Control.Arrow ((>>>))

import Language.Granule.Utils

data DocType
  = Markdown
  | GranuleBlockTwiddle
  | GranuleBlockTick

-- | Extract fenced code blocks from markdown files on a
-- line-by-line basis. Maps other lines to the empty string, such that line
-- numbers are preserved.
unMarkdown :: (?globals :: Globals) => (String -> String)
unMarkdown = processGranuleMarkdown (const "") literateEnvName id

-- | Transform the input by the given processing functions for Granule and
-- Markdown (currently operating on a line-by-line basis)
processGranuleMarkdown
  :: (String -> String) -- the processing function to apply to each line of markdown
  -> String             -- the name of the code env, e.g. "granule"
  -> (String -> String) -- the processing function to apply to each line of granule code
  -> (String -> String)
processGranuleMarkdown fMd env fGr = lines >>> (`zip` [1..]) >>> go Markdown >>> unlines
  where
    go :: DocType -> [(String, Int)] -> [String]
    go Markdown ((line, lineNumber) : ls)
      | strip line == "~~~" <> env || strip line == "~~~ " <> env
        = fMd line : go GranuleBlockTwiddle ls
      | strip line == "```" <> env || strip line == "``` " <> env
        = fMd line : go GranuleBlockTick ls
      | otherwise
        = fMd line : go Markdown ls
    go GranuleBlockTwiddle ((line, lineNumber) : ls)
      | strip line == "~~~"
        = fMd line : go Markdown ls
      | strip line == "~~~" <> env
        || strip line == "~~~ " <> env
        || strip line == "```" <> env
        || strip line == "``` " <> env
          = error
            $ "Unexpected `"
            <> line
            <> "` on line "
            <> show lineNumber
            <> " while inside a " <> env <> " code block (~~~)"
      | otherwise
        = fGr line : go GranuleBlockTwiddle ls
    go GranuleBlockTick ((line, lineNumber) : ls)
      | strip line == "```"
        = fMd line : go Markdown ls
      | strip line == "~~~" <> env
        || strip line == "~~~ " <> env
        || strip line == "```" <> env
        || strip line == "``` " <> env
          = error
            $ "Unexpected `"
            <> line
            <> "` on line "
            <> show lineNumber
            <> " while inside a " <> env <> " code block (```)"
      | otherwise
        = fGr line : go GranuleBlockTick ls
    go _ [] = []

    -- Remove trailing whitespace (hey, should we be using @Text@?)
    strip :: String -> String
    strip = reverse . dropWhile isSpace . reverse . dropWhile isSpace
