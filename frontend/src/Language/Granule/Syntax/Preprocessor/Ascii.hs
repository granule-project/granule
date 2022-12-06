{-# LANGUAGE OverloadedStrings #-}

module Language.Granule.Syntax.Preprocessor.Ascii
  ( asciiToUnicode
  , unicodeToAscii
  , asciiUnicodeTableMarkdown
  ) where

import Data.String (fromString)
import Data.Text.Lazy (pack, unpack)
import Text.Replace (Replace(..), replaceWithList)

asciiToUnicode :: String -> String
asciiToUnicode = unpack . (replaceWithList (asciiUnicodeTableReplacements id)) . pack

unicodeToAscii :: String -> String
unicodeToAscii = unpack . (replaceWithList (asciiUnicodeTableReplacements swap)) . pack
  where swap (a, b) = (b, a)

-- NOTE: Update the documentation with 'asciiUnicodeTableMarkdown' if you touch this.
asciiUnicodeTableReplacements :: ((String, String) -> (String, String)) -> [Replace]
asciiUnicodeTableReplacements transformer =
  flip map asciiUnicodeTable
    (\(to, from) -> let (to', from') = transformer (to, from)
                    in Replace (fromString to') (fromString from'))


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

