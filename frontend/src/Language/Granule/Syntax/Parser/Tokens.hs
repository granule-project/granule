module Language.Granule.Syntax.Parser.Tokens
    ( Token(..)
    , Keyword(..)
    , layoutKeywords
    , Symbol(..)
    ) where

import Language.Granule.Syntax.Literal (Literal)
import Language.Granule.Syntax.Position

data Keyword
        = KwLet | KwIn | KwWhere
        | KwCase | KwOf | KwImport
        | KwModule | KwForall
        | KwData | KwHiding
        | KwIf | KwThen | KwElse
    deriving (Eq, Show)

layoutKeywords :: [Keyword]
layoutKeywords = [ KwWhere, KwIn ]

data Symbol
        = SymDot | SymSemi | SymVirtualSemi | SymBar
        | SymColon | SymArrow | SymEqual | SymLambda
        | SymUnderscore | SymQuestionMark   | SymAt
        | SymOpenParen        | SymCloseParen
        | SymOpenBrace        | SymCloseBrace
        | SymOpenVirtualBrace | SymCloseVirtualBrace
        | SymPlus | SymStar | SymAbsurd | SymComma | SymDoubleColon
        | SymOpenBracket | SymCloseBracket
        | SymBoxLeft | SymBoxRight
        | SymConstrain | SymSub | SymLangle | SymRangle
        | SymLesserEq | SymGreaterEq | SymEquiv | SymNeq
        | SymRing | SymHoleStart | SymHoleEnd | SymEmptyHole
        | SymInfinity | SymForwardSlash | SymBind | SymCross
        | SymSig | SymBackTick | SymCaret | SymJoin | SymDotDot
        | SymMeet
        | SymEndComment -- ^ A misplaced end-comment "-}".
    deriving (Eq, Show)

data Token
          -- Keywords
        = TokKeyword Keyword Interval
          -- Identifiers and operators
        | TokId         (Interval, String)
        | TokQId        [(Interval, String)]
                        -- Non-empty namespace. The intervals for
                        -- "A.B.x" correspond to "A.", "B." and "x".
          -- Literals
        | TokInt Literal
        | TokFloat Literal
        | TokCharLiteral Literal
        | TokStringLiteral Literal
        | TokConstr (Interval, String)
        | TokLiteral    Literal
          -- Special symbols
        | TokSymbol Symbol Interval
          -- Other tokens
        | TokString (Interval, String)  -- arbitrary string, used in pragmas
        | TokSetN (Interval, Integer)
        | TokPropN (Interval, Integer)
        | TokTeX (Interval, String)
        | TokMarkup (Interval, String)
        | TokComment (Interval, String)
        | TokDummy      -- Dummy token to make Happy not complain
                        -- about overlapping cases.
        | TokEOF Interval
    deriving (Eq, Show)

instance HasRange Token where
  getRange (TokKeyword _ i)    = getRange i
  getRange (TokId (i, _))      = getRange i
  getRange (TokConstr (i, _))      = getRange i
  getRange (TokQId iss)        = getRange (map fst iss)
  getRange (TokLiteral lit)    = getRange lit
  getRange (TokInt lit)        = getRange lit
  getRange (TokFloat lit)      = getRange lit
  getRange (TokCharLiteral lit)   = getRange lit
  getRange (TokStringLiteral lit) = getRange lit
  getRange (TokSymbol _ i)     = getRange i
  getRange (TokString (i, _))  = getRange i
  getRange (TokSetN (i, _))    = getRange i
  getRange (TokPropN (i, _))   = getRange i
  getRange (TokTeX (i, _))     = getRange i
  getRange (TokMarkup (i, _))  = getRange i
  getRange (TokComment (i, _)) = getRange i
  getRange TokDummy            = noRange
  getRange (TokEOF i)          = getRange i
