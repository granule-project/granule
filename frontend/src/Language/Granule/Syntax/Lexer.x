{
{-# OPTIONS_GHC -w #-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Granule.Syntax.Lexer (Token(..),scanTokens,getPos,
                     getPosToSpan,symString,constrString) where
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.FirstParameter
import GHC.Generics (Generic)
import Data.Text (Text)

}

%wrapper "posn"

$digit  = 0-9
$alpha  = [a-zA-Z\_\-\=]
$lower  = [a-z]
$upper  = [A-Z]
$eol    = [\n]
$alphanum  = [$alpha $digit \_]
$fruit = [\127815-\127827] -- 🍇🍈🍉🍊🍋🍌🍍🍎🍏🍐🍑🍒🍓
@sym    = $lower ($alphanum | \')* | $fruit
@constr = ($upper ($alphanum | \')* | \(\))
@float   = \-? $digit+ \. $digit+
@int    = \-? $digit+
@charLiteral = \' (\\.|[^\']| . ) \'
@stringLiteral = \"(\\.|[^\"]|\n)*\"
@importFilePath = ($alphanum | \' | \.)*

tokens :-

  $white*$eol                   { \p s -> TokenNL p }
  $eol+                         { \p s -> TokenNL p }
  $white+                       ;
  "--".*                        ;
  "{-" (\\.|[^\{\-]|\n)* "-}"   ;
  import$white+@importFilePath  { \p s -> TokenImport p s }
  language$white+               { \p s -> TokenPragma p s }
  @constr                       { \p s -> TokenConstr p s }
  forall                        { \p s -> TokenForall p }
  ∀                             { \p s -> TokenForall p }
  let                           { \p s -> TokenLet p }
  data                          { \p s -> TokenData p }
  where                         { \p s -> TokenWhere p }
  module                        { \p s -> TokenModule p }
  hiding                        { \p s -> TokenHiding p }
  in                            { \p s -> TokenIn p }
  if                            { \p s -> TokenIf p }
  then                          { \p s -> TokenThen p }
  else                          { \p s -> TokenElse p }
  case                          { \p s -> TokenCase p }
  of                            { \p s -> TokenOf p }
  try                           { \p s -> TokenTry p }
  as                            { \p s -> TokenAs p }
  catch                         { \p s -> TokenCatch p }
  clone                          { \p s -> TokenCopy p }
  ∞                             { \p s -> TokenInfinity p }
  @float                        { \p s -> TokenFloat p s }
  @int                          { \p s -> TokenInt p $ read s }
  @charLiteral                  { \p s -> TokenCharLiteral p $ read s }
  @stringLiteral                { \p s -> TokenStringLiteral p $ read s }
  "@"                           { \p s -> TokenAt p }
  "->"                          { \p s -> TokenArrow p }
  "→"                           { \p s -> TokenArrow p }
  "<-"                          { \p s -> TokenBind p }
  "←"                           { \p s -> TokenBind p }
  \;                            { \p s -> TokenSemicolon p }
  \=                            { \p s -> TokenEq p }
  "/="                          { \p s -> TokenNeq p }
  "≠"                           { \p _ -> TokenNeq p }
  \\                            { \p s -> TokenLambda p }
  "λ"                           { \p s -> TokenLambda p }
  \[                            { \p s -> TokenBoxLeft p }
  \]                            { \p s -> TokenBoxRight p }
  [\+]                          { \p s -> TokenAdd p }
  [\-]                          { \p s -> TokenSub p }
  [\*]                          { \p s -> TokenMul p }
  \(                            { \p s -> TokenLParen p }
  \)                            { \p s -> TokenRParen p }
  \{                            { \p s -> TokenLBrace p }
  \}                            { \p s -> TokenRBrace p }
  \<                            { \p s -> TokenLangle p }
  \>                            { \p s -> TokenRangle p }
  \,                            { \p s -> TokenComma p }
  \×                            { \p s -> TokenCross p }
  \.                            { \p s -> TokenPeriod p }
  \:                            { \p s -> TokenSig p }
  @sym				                  { \p s -> TokenSym p s }
  \_                            { \p _ -> TokenUnderscore p }
  \|                            { \p s -> TokenPipe p }
  \/                            { \p s -> TokenForwardSlash p }
  "≤"                           { \p s -> TokenLesserEq p }
  "<="                          { \p s -> TokenLesserEq p }
  "≥"                           { \p s -> TokenGreaterEq p }
  ">="                          { \p s -> TokenGreaterEq p }
  "=="                          { \p s -> TokenEquiv p }
  "≡"                           { \p s -> TokenEquiv p }
  "`"                           { \p s -> TokenBackTick p }
  "^"                           { \p s -> TokenCaret p }
  ".."                          { \p s -> TokenDotDot p }
  "∨"                           { \p _ -> TokenJoin p }
  "\\/"                         { \p _ -> TokenJoin p }
  "∧"                           { \p _ -> TokenMeet p }
  "/\\"                         { \p _ -> TokenMeet p }
  "=>"                          { \p s -> TokenConstrain p }
  "⇒"                           { \p s -> TokenConstrain p }
  "∘"                           { \p _ -> TokenRing p }
  "?"                           { \p _ -> TokenEmptyHole p }
  "{!"                          { \p _ -> TokenHoleStart p }
  "!}"                          { \p _ -> TokenHoleEnd p}
  "!"                           { \p _ -> TokenBang p}
  "&"                           { \p _ -> TokenBorrow p}
  "#"                           { \p _ -> TokenHash p }

{

data Token
  = TokenLet    AlexPosn
  | TokenIn     AlexPosn
  | TokenIf     AlexPosn
  | TokenThen   AlexPosn
  | TokenElse   AlexPosn
  | TokenData   AlexPosn
  | TokenTypeDecl AlexPosn
  | TokenWhere  AlexPosn
  | TokenModule AlexPosn
  | TokenHiding AlexPosn
  | TokenCase   AlexPosn
  | TokenOf     AlexPosn
  | TokenTry    AlexPosn
  | TokenAs     AlexPosn
  | TokenCatch  AlexPosn
  | TokenInfinity AlexPosn
  | TokenLambda AlexPosn
  | TokenLetBox AlexPosn
  | TokenBind   AlexPosn
  | TokenBox    AlexPosn
  | TokenInt    AlexPosn Int
  | TokenFloat  AlexPosn String
  | TokenSym    AlexPosn String
  | TokenArrow  AlexPosn
  | TokenConstrain AlexPosn
  | TokenForall AlexPosn
  | TokenEq     AlexPosn
  | TokenNeq     AlexPosn
  | TokenAdd    AlexPosn
  | TokenSub    AlexPosn
  | TokenMul    AlexPosn
  | TokenCharLiteral AlexPosn Char
  | TokenStringLiteral AlexPosn Text
  | TokenLParen AlexPosn
  | TokenRParen AlexPosn
  | TokenNL     AlexPosn
  | TokenConstr AlexPosn String
  | TokenBackTick AlexPosn
  | TokenSig    AlexPosn
  | TokenBoxLeft AlexPosn
  | TokenBoxRight AlexPosn
  | TokenLBrace   AlexPosn
  | TokenRBrace   AlexPosn
  | TokenLangle   AlexPosn
  | TokenRangle   AlexPosn
  | TokenComma    AlexPosn
  | TokenCross AlexPosn
  | TokenPeriod   AlexPosn
  | TokenPipe     AlexPosn
  | TokenUnderscore AlexPosn
  | TokenSemicolon  AlexPosn
  | TokenForwardSlash AlexPosn
  | TokenLesserEq AlexPosn
  | TokenGreaterEq AlexPosn
  | TokenEquiv AlexPosn
  | TokenCaret AlexPosn
  | TokenDotDot AlexPosn
  | TokenJoin AlexPosn
  | TokenMeet AlexPosn
  | TokenRing AlexPosn
  | TokenImport AlexPosn String
  | TokenPragma AlexPosn String
  | TokenEmptyHole AlexPosn
  | TokenHoleStart AlexPosn
  | TokenHoleEnd AlexPosn
  | TokenAt AlexPosn
  | TokenBang AlexPosn
  | TokenBorrow AlexPosn
  | TokenCopy AlexPosn
  | TokenHash AlexPosn

  deriving (Eq, Show, Generic)

symString :: Token -> String
symString (TokenSym _ x) = x

constrString :: Token -> String
constrString (TokenConstr _ x) = x

scanTokens = alexScanTokens >>= (return . trim)

trim :: [Token] -> [Token]
trim = reverse . trimNL . reverse . trimNL

trimNL :: [Token] -> [Token]
trimNL [] = []
trimNL (TokenNL _ : ts) = trimNL ts
trimNL ts = ts

instance FirstParameter Token AlexPosn

getPos :: Token -> (Int, Int)
getPos t = (l, c)
  where (AlexPn _ l c) = getFirstParameter t

getPosToSpan :: Token -> ((Int, Int), (Int, Int))
getPosToSpan t = (getPos t, getPos t)

}
