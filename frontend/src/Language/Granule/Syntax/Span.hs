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