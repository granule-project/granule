{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Granule.Interpreter.Preprocess where

import Control.Exception (SomeException, throwIO, try)
import Control.Monad (when)
import Data.List (intercalate)
import System.Directory (removeFile, renameFile)
import System.FilePath (splitFileName)
import System.IO (hClose, hPutStr, openTempFile)

import Language.Granule.Syntax.Preprocessor.Latex
import Language.Granule.Syntax.Preprocessor.Markdown


-- | Preprocess the source file based on the file extension.
preprocess :: Maybe (String -> String) -> Bool -> String -> FilePath -> IO String
preprocess mbRewriter keepOldFile file env
  = case lookup extension acceptedFormats of
      Just (stripNonGranule, preprocessOnlyGranule) -> do
        src <- readFile file
        case mbRewriter of
          Just rewriter -> do
            let processedSrc = preprocessOnlyGranule rewriter src
            -- open a temporary file
            (tempFile, tempHd) <- uncurry openTempFile (splitFileName file)
            -- write the processed source to the temporary file
            try (hPutStr tempHd processedSrc) >>= \case
              Right () -> do
                hClose tempHd
                -- if we are keeping the original source file, then rename it
                when keepOldFile (renameFile file (file <> ".bak"))
                -- move the temp file to the original source file path
                renameFile tempFile file
                return $ stripNonGranule processedSrc
              Left (e :: SomeException) -> do
                hClose tempHd
                removeFile tempFile
                throwIO e
          Nothing -> return $ stripNonGranule src
      Nothing -> error
        $ "Unrecognised file extension: "
        <> extension
        <> ". Expected one of "
        <> intercalate ", " (map fst acceptedFormats)
        <> "."
  where
    extension = reverse . takeWhile (/= '.') . reverse $ file

    -- (file extension, (stripNonGranule, destructive preprocessor))
    acceptedFormats =
      [ ("gr",    (id,             id))
      , ("md",    (unMarkdown env, processGranuleMarkdown id env))
      , ("tex",   (unLatex env,    processGranuleLatex id env))
      , ("latex", (unLatex env,    processGranuleLatex id env))
      ]
