{-# LANGUAGE FlexibleContexts #-}

module Language.Granule.Syntax.Span where

import Language.Granule.Syntax.FirstParameter

type Pos = (Int, Int) -- (line, column)
type Span = (Pos, Pos)
nullSpan :: Span
nullSpan = ((0, 0), (0, 0))

getSpan :: FirstParameter t Span => t -> Span
getSpan = getFirstParameter

getEnd ::  FirstParameter t Span => t -> Pos
getEnd = snd . getSpan

getStart ::  FirstParameter t Span => t -> Pos
getStart = fst . getSpan
