{-# LANGUAGE OverloadedStrings #-}

module Language.Granule.Syntax.Preprocessor.Ascii (unAscii) where

import Text.Replace (Replace(..), replaceWithList)

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
    , "\\" ~> "λ"
    ]
  where
    (~>) = Replace
