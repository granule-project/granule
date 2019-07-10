{-# LANGUAGE OverloadedStrings #-}

module Language.Granule.Syntax.Preprocessor.Ascii
  ( asciiToUnicode
  , unicodeToAscii
  , asciiUnicodeTableMarkdown
  ) where

import Control.Arrow (first, second)
import Data.String (fromString)
import Text.Replace (Replace(..), replaceWithList)

asciiToUnicode :: String -> String
asciiToUnicode = replaceWithList $ map (uncurry Replace . first fromString) asciiUnicodeTable

unicodeToAscii :: String -> String
unicodeToAscii = replaceWithList $ map (uncurry (flip Replace) . second fromString) asciiUnicodeTable

-- NOTE: Update the documentation with 'asciiUnicodeTableMarkdown' if you touch this.
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

