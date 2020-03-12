{-
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Granule.Syntax.Literal where

import Control.DeepSeq
import Data.Char
import Data.Word

import Data.Data (Data)

import Numeric.IEEE ( IEEE(identicalIEEE) )

-- import Language.Granule.Syntax.Position
-- import Language.Granule.Syntax.Common
-- import Language.Granule.Syntax.Abstract.Name
import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
-- import Language.Granule.Utils.FileName

type Range = Span

data Literal = LitNat    Range !Integer
             | LitWord64 Range !Word64
             | LitFloat  Range !Double
             | LitString Range String
             | LitChar   Range !Char
  deriving Data

instance Show Literal where
  showsPrec p l = showParen (p > 9) $ case l of
    LitNat _ n    -> sh "LitNat _" n
    LitWord64 _ n -> sh "LitWord64 _" n
    LitFloat _ x  -> sh "LitFloat _" x
    LitString _ s -> sh "LitString _" s
    LitChar _ c   -> sh "LitChar _" c
    where
      sh :: Show a => String -> a -> ShowS
      sh c x = showString (c ++ " ") . shows x

instance Pretty Literal where
    pretty (LitNat _ n)     = show n
    pretty (LitWord64 _ n)  = show n
    pretty (LitFloat _ d)   = show d
    pretty (LitString _ s)  = showString' s ""
    pretty (LitChar _ c)    = "'" ++ showChar' c "'"

showString' :: String -> ShowS
showString' s =
    foldr (.) id $ [ showString "\"" ] ++ map showChar' s ++ [ showString "\"" ]

showChar' :: Char -> ShowS
showChar' '"'   = showString "\\\""
showChar' c
    | escapeMe c = showLitChar c
    | otherwise  = showString [c]
    where
        escapeMe c = not (isPrint c) || c == '\\'

instance Eq Literal where
  LitNat _ n    == LitNat _ m    = n == m
  -- ASR (2016-09-29). We use bitwise equality for comparing Double
  -- because Haskell's Eq, which equates 0.0 and -0.0, allows to prove
  -- a contradiction (see Issue #2169).
  LitWord64 _ n == LitWord64 _ m = n == m
  LitFloat _ x  == LitFloat _ y  = identicalIEEE x y || (isNaN x && isNaN y)
  LitString _ s == LitString _ t = s == t
  LitChar _ c   == LitChar _ d   = c == d
  _             == _             = False

instance Ord Literal where
  LitNat _ n    `compare` LitNat _ m    = n `compare` m
  LitWord64 _ n `compare` LitWord64 _ m = n `compare` m
  LitFloat _ x  `compare` LitFloat _ y  = compareFloat x y
  LitString _ s `compare` LitString _ t = s `compare` t
  LitChar _ c   `compare` LitChar _ d   = c `compare` d
  compare LitNat{}    _ = LT
  compare _ LitNat{}    = GT
  compare LitWord64{} _ = LT
  compare _ LitWord64{} = GT
  compare LitFloat{}  _ = LT
  compare _ LitFloat{}  = GT
  compare LitString{} _ = LT
  compare _ LitString{} = GT

-- NOTE: This is not the same ordering as primFloatNumericalEquality!
-- This ordering must be a total order of all allowed float values,
-- while primFloatNumericalEquality is only a preorder
compareFloat :: Double -> Double -> Ordering
compareFloat x y
  | identicalIEEE x y          = EQ
  | isNegInf x                 = LT
  | isNegInf y                 = GT
  | isNaN x && isNaN y         = EQ
  | isNaN x                    = LT
  | isNaN y                    = GT
  | isNegativeZero x && x == y = LT
  | isNegativeZero y && x == y = GT
  | otherwise                  = compare x y
  where
    isNegInf z = z < 0 && isInfinite z

instance FirstParameter Literal Span where
  getFirstParameter (LitNat    r _) = r
  getFirstParameter (LitWord64 r _) = r
  getFirstParameter (LitFloat  r _) = r
  getFirstParameter (LitString r _) = r
  getFirstParameter (LitChar   r _) = r

  setFirstParameter r (LitNat    _ x) = LitNat    r x
  setFirstParameter r (LitWord64 _ x) = LitWord64 r x
  setFirstParameter r (LitFloat  _ x) = LitFloat  r x
  setFirstParameter r (LitString _ x) = LitString r x
  setFirstParameter r (LitChar   _ x) = LitChar   r x

-- | Ranges are not forced.
instance NFData Literal where
  rnf (LitNat _ _)    = ()
  rnf (LitWord64 _ _) = ()
  rnf (LitFloat _ _)  = ()
  rnf (LitString _ a) = rnf a
  rnf (LitChar _ _)   = ()
  rnf -}

{-# LANGUAGE DeriveDataTypeable #-}

module Language.Granule.Syntax.Literal where

import Control.DeepSeq
import Data.Char
import Data.Word

import Data.Data (Data)

import Numeric.IEEE ( IEEE(identicalIEEE) )

import Language.Granule.Syntax.Position
import Language.Granule.Syntax.Pretty

data Literal = LitNat    Range !Integer
             | LitWord64 Range !Word64
             | LitFloat  Range !Double
             | LitString Range String
             | LitChar   Range !Char
  deriving Data

instance Show Literal where
  showsPrec p l = showParen (p > 9) $ case l of
    LitNat _ n    -> sh "LitNat _" n
    LitWord64 _ n -> sh "LitWord64 _" n
    LitFloat _ x  -> sh "LitFloat _" x
    LitString _ s -> sh "LitString _" s
    LitChar _ c   -> sh "LitChar _" c
    where
      sh :: Show a => String -> a -> ShowS
      sh c x = showString (c ++ " ") . shows x

instance Pretty Literal where
    pretty (LitNat _ n)     = text $ show n
    pretty (LitWord64 _ n)  = text $ show n
    pretty (LitFloat _ d)   = text $ show d
    pretty (LitString _ s)  = text $ showString' s ""
    pretty (LitChar _ c)    = text $ "'" ++ showChar' c "'"

showString' :: String -> ShowS
showString' s =
    foldr (.) id $ [ showString "\"" ] ++ map showChar' s ++ [ showString "\"" ]

showChar' :: Char -> ShowS
showChar' '"'   = showString "\\\""
showChar' c
    | escapeMe c = showLitChar c
    | otherwise  = showString [c]
    where
        escapeMe c = not (isPrint c) || c == '\\'

instance Eq Literal where
  LitNat _ n    == LitNat _ m    = n == m
  -- ASR (2016-09-29). We use bitwise equality for comparing Double
  -- because Haskell's Eq, which equates 0.0 and -0.0, allows to prove
  -- a contradiction (see Issue #2169).
  LitWord64 _ n == LitWord64 _ m = n == m
  LitFloat _ x  == LitFloat _ y  = identicalIEEE x y || (isNaN x && isNaN y)
  LitString _ s == LitString _ t = s == t
  LitChar _ c   == LitChar _ d   = c == d
  _             == _             = False

instance Ord Literal where
  LitNat _ n    `compare` LitNat _ m    = n `compare` m
  LitWord64 _ n `compare` LitWord64 _ m = n `compare` m
  LitFloat _ x  `compare` LitFloat _ y  = compareFloat x y
  LitString _ s `compare` LitString _ t = s `compare` t
  LitChar _ c   `compare` LitChar _ d   = c `compare` d
  compare LitNat{}    _ = LT
  compare _ LitNat{}    = GT
  compare LitWord64{} _ = LT
  compare _ LitWord64{} = GT
  compare LitFloat{}  _ = LT
  compare _ LitFloat{}  = GT
  compare LitString{} _ = LT
  compare _ LitString{} = GT

-- NOTE: This is not the same ordering as primFloatNumericalEquality!
-- This ordering must be a total order of all allowed float values,
-- while primFloatNumericalEquality is only a preorder
compareFloat :: Double -> Double -> Ordering
compareFloat x y
  | identicalIEEE x y          = EQ
  | isNegInf x                 = LT
  | isNegInf y                 = GT
  | isNaN x && isNaN y         = EQ
  | isNaN x                    = LT
  | isNaN y                    = GT
  | isNegativeZero x && x == y = LT
  | isNegativeZero y && x == y = GT
  | otherwise                  = compare x y
  where
    isNegInf z = z < 0 && isInfinite z

instance HasRange Literal where
  getRange (LitNat    r _) = r
  getRange (LitWord64 r _) = r
  getRange (LitFloat  r _) = r
  getRange (LitString r _) = r
  getRange (LitChar   r _) = r

instance SetRange Literal where
  setRange r (LitNat    _ x) = LitNat    r x
  setRange r (LitWord64 _ x) = LitWord64 r x
  setRange r (LitFloat  _ x) = LitFloat  r x
  setRange r (LitString _ x) = LitString r x
  setRange r (LitChar   _ x) = LitChar   r x

instance KillRange Literal where
  killRange (LitNat    r x) = LitNat    (killRange r) x
  killRange (LitWord64 r x) = LitWord64 (killRange r) x
  killRange (LitFloat  r x) = LitFloat  (killRange r) x
  killRange (LitString r x) = LitString (killRange r) x
  killRange (LitChar   r x) = LitChar   (killRange r) x

-- | Ranges are not forced.

instance NFData Literal where
  rnf (LitNat _ _)    = ()
  rnf (LitWord64 _ _) = ()
  rnf (LitFloat _ _)  = ()
  rnf (LitString _ a) = rnf a
  rnf (LitChar _ _)   = ()
