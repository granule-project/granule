{-# LANGUAGE FlexibleContexts #-}

module Language.Granule.Syntax.Span where

import Language.Granule.Syntax.FirstParameter

type Pos = (Int, Int) -- (line, column)

data Span = Span { startPos :: Pos
                 , endPos :: Pos
                 , filename :: String
                 }
  deriving (Eq, Show)

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
