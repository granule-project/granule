{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Granule.Interpreter.Preprocess where

import Control.Exception (SomeException, throwIO, try)
import Control.Monad (when)
import Data.List (intercalate)
import System.Directory (removeFile, renameFile)
import System.FilePath (splitFileName)
import System.IO (hClose, hPutStr, openTempFile)

import Language.Granule.Syntax.Preprocessor.Ascii
import Language.Granule.Syntax.Preprocessor.Latex
import Language.Granule.Syntax.Preprocessor.Markdown


-- | Preprocess the source file based on the file extension.
preprocess :: Bool -> Bool -> FilePath -> IO String
preprocess performAsciiToUnicodeOnFile keepOldFile file
  = case lookup extension preprocessors of
    Just (stripNonGranule, asciiToUnicode) -> do
      src <- readFile file
      when performAsciiToUnicodeOnFile $ do
        (tempFile, tempHd) <- uncurry openTempFile (splitFileName file)
        try (hPutStr tempHd (asciiToUnicode src)) >>= \case
          Right () -> do
            hClose tempHd
            when keepOldFile (renameFile file (file <> ".bak"))
            renameFile tempFile file
          Left (e :: SomeException) -> do
            hClose tempHd
            removeFile tempFile
            throwIO e
      return $ stripNonGranule src
    Nothing -> error
      $ "Unrecognised file extension: "
      <> extension
      <> ". Expected one of "
      <> intercalate ", " (map fst preprocessors)
      <> "."
  where
    extension = reverse . takeWhile (/= '.') . reverse $ file

    preprocessors =
      [ ("gr",    (id,         unAscii))
      , ("md",    (unMarkdown, processGranuleMarkdown unAscii id))
      , ("tex",   (unLatex,    processGranuleLatex unAscii id))
      , ("latex", (unLatex,    processGranuleLatex unAscii id))
      ]
