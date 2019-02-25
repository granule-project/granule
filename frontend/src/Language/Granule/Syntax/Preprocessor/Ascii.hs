{-# LANGUAGE OverloadedStrings #-}

module Language.Granule.Syntax.Preprocessor.Ascii (unAscii, asciiUnicodeTableMarkdown) where

import Control.Arrow (first)
import Data.String (fromString)
import Text.Replace (Replace(..), replaceWithList)

unAscii :: String -> String
unAscii = replaceWithList $ map (uncurry Replace . first fromString) asciiUnicodeTable

-- NOTE: Update the documentation if you touch this.
asciiUnicodeTable :: [(String,String)]
asciiUnicodeTable =
    [ ("forall" , "∀")
    , ("Inf" , "∞")
    , ("->" , "→")
    , ("=>" , "⇒")
    , ("<-" , "←")
    , ("/\\" , "∧")
    , ("\\/" , "∨")
    , ("<=" , "≤")
    , (">=" , "≥")
    , ("==" , "≡")
    , ("\\" , "λ")
    ]

asciiUnicodeTableMarkdown :: String
asciiUnicodeTableMarkdown
    = unlines
    $ [ ("| ASCII | Unicode |")
      , ("|:---:|:---:|")
      ]
    <> map mkRow asciiUnicodeTable
  where
    mkRow (x,y) = mconcat ["| `", x, "` | `", y, "` |"]
    -- escapeBackslash = \case
    --   [] -> []
    --   '\\' : cs -> '\\' : '\\' : escapeBackslash cs
    --   c : cs -> c : escapeBackslash cs

