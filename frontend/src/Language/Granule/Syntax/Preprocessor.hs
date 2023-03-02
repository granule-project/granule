{-# LANGUAGE ScopedTypeVariables #-}

module Language.Granule.Syntax.Preprocessor where

import Data.List (intercalate)

import Language.Granule.Syntax.Preprocessor.Latex
import Language.Granule.Syntax.Preprocessor.Markdown
import Language.Granule.Syntax.Preprocessor.Ascii

import Language.Granule.Utils

-- | Preprocess the source file based on the file extension.
preprocess :: (?globals :: Globals) => FilePath -> IO String
preprocess filePath
  = case lookup extension acceptedFormats of
      Just (stripNonGranule, destructivePreprocessor) -> do
        src <- readFile filePath
        case rewriter of
          Just rewriter -> do
            let rewriterF = case rewriter of
                  AsciiToUnicode -> asciiToUnicode
                  UnicodeToAscii -> unicodeToAscii
            let processedSrc = destructivePreprocessor rewriterF src
            written <- writeSrcFile filePath keepBackupOfProcessedFile processedSrc
            return $ stripNonGranule written
          Nothing -> return $ stripNonGranule src
      Nothing -> error
        $ "Unrecognised file extension: "
        <> extension
        <> ". Expected one of "
        <> intercalate ", " (map fst acceptedFormats)
        <> "."
  where

    extension = reverse . takeWhile (/= '.') . reverse $ filePath

    -- (file extension, (stripNonGranule, destructivePreprocessor))
    acceptedFormats =
      [ ("gr",    (id,         id))
      , ("md",    (unMarkdown, processGranuleMarkdown id literateEnvName))
      , ("tex",   (unLatex,    processGranuleLatex id literateEnvName))
      , ("latex", (unLatex,    processGranuleLatex id literateEnvName))
      ]
