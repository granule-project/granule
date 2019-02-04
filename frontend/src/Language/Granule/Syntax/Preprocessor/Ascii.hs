{-# LANGUAGE OverloadedStrings #-}

module Language.Granule.Syntax.Preprocessor.Ascii (unAscii, unAsciiFile) where

import System.Directory (renameFile)
import System.FilePath (splitFileName)
import System.IO (hClose, hPutStr, openTempFile)
import Text.Replace (replaceWithList)

unAscii :: String -> String
unAscii = replaceWithList
    [ "forall" ~> "∀"
    , "Inf" ~> "∞"
    , "->" ~> "→"
    , "=>" ~> "⇒"
    , "<-" ~> "←"
    , "/\\" ~> "∧"
    , "\\/" ~> "∨"
    , "<=" ~> "≤"
    , ">=" ~> "≥"
    , "==" ~> "≡"
    ]
  where
    (~>) = Replace

unAsciiFile :: FilePath -> IO String
unAsciiFile fp = do
  src <- readFile fp
  (tempFp, tempHd) <- uncurry openTempFile (splitFileName fp)
  hPutStr tempHd (unAscii src)
  hClose tempHd
  renameFile tempFp fp
  pure $ unAscii src
