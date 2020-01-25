{-# LANGUAGE ScopedTypeVariables #-}

module Language.Granule.Syntax.Preprocessor where

import Data.List (intercalate)

import Language.Granule.Syntax.Preprocessor.Latex
import Language.Granule.Syntax.Preprocessor.Markdown

import Language.Granule.Utils

-- | Preprocess the source file based on the file extension.
preprocess :: Maybe (String -> String) -> Bool -> String -> FilePath -> IO String
preprocess mbRewriter keepOldFile file env
  = case lookup extension acceptedFormats of
      Just (stripNonGranule, preprocessOnlyGranule) -> do
        src <- readFile file
        case mbRewriter of
          Just rewriter -> do
            let processedSrc = preprocessOnlyGranule rewriter src
            written <- writeSrcFile file keepOldFile processedSrc
            return $ stripNonGranule written
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
