{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Language.Granule.Syntax.Span where

import Control.Arrow ((***))
import qualified Text.Reprinter as Rp (Data, Span, Col(..), Line(..))

import Language.Granule.Syntax.FirstParameter

type Pos = (Int, Int) -- (line, column)

data Span = Span { startPos :: Pos
                 , endPos :: Pos
                 , filename :: String }
  deriving (Eq, Show, Rp.Data)

nullSpanLocs :: (Pos, Pos)
nullSpanLocs = ((0, 0), (0, 0))

nullSpanNoFile :: Span
nullSpanNoFile = Span (0, 0) (0, 0) ""

nullSpanInFile :: Span -> Span
nullSpanInFile s = Span (0, 0) (0, 0) (filename s)

getSpan :: FirstParameter t Span => t -> Span
getSpan = getFirstParameter

getEnd ::  FirstParameter t Span => t -> Pos
getEnd = endPos . getSpan

getStart ::  FirstParameter t Span => t -> Pos
getStart = startPos . getSpan

convSpan :: Span -> Rp.Span
convSpan Span{startPos = sp, endPos = ep} =
  ((Rp.Line *** Rp.Col) sp, (Rp.Line *** Rp.Col) ep)

-- Determines whether a given position is within the bounds of a span.
spanContains :: Pos -> Span -> Bool
spanContains (posL, posC) (Span (startL, startC) (endL, endC) _) =
  startL <= posL && endL >= posL && startC <= posC && endC >= posC

-- A span encompasses another if it contains both positions of the other span.
encompasses :: Span -> Span -> Bool
encompasses outer (Span pos1 pos2 _) =
  spanContains pos1 outer && spanContains pos2 outer
