{
{-# OPTIONS_GHC -w #-}
module Syntax.Lexer (Token(..),scanTokens) where
import Syntax.Expr
import Debug.Trace
}

%wrapper "basic"

$digit  = 0-9
$alpha  = [a-zA-Z]
$lower  = [a-z]
$upper  = [A-Z]
$eol    = [\n]
$alphanum  = [$alpha $digit \_ \']
@sym    = $lower $alphanum*
@constr = $upper $alphanum*

tokens :-

  $eol+                         { \s -> TokenNL }
  $white+                       ;
  "--".*                         ;
  @constr                       { \s -> TokenConstr s }
  let                           { \s -> TokenLet }
  in                            { \s -> TokenIn }
  case                          { \s -> TokenCase }
  of                            { \s -> TokenOf }
  $digit+                       { \s -> TokenNum (read s) }
  "->"                          { \s -> TokenArrow }
  \;                            { \s -> TokenSemicolon }
  \=                            { \s -> TokenEq }
  \\                            { \s -> TokenLambda }
  \[                            { \s -> TokenBoxLeft }
  \]                            { \s -> TokenBoxRight }
  [\+]                          { \s -> TokenAdd }
  [\-]                          { \s -> TokenSub }
  [\*]                          { \s -> TokenMul }
  \(                            { \s -> TokenLParen }
  \)                            { \s -> TokenRParen }
  \{                            { \s -> TokenLBrace }
  \}                            { \s -> TokenRBrace }
  \<                            { \s -> TokenLangle }
  \>                            { \s -> TokenRangle }
  \,                            { \s -> TokenComma }
  \:                            { \s -> TokenSig }
  @sym				{ \s -> TokenSym s }
  \_                            { \_ -> TokenUnderscore }
  \|                            { \s -> TokenPipe }

{

data Token = TokenLet
           | TokenIn
	   | TokenCase
	   | TokenOf
           | TokenLambda
	   | TokenLetBox
	   | TokenBox
           | TokenNum Int
           | TokenSym String
           | TokenArrow
           | TokenEq
           | TokenAdd
           | TokenSub
           | TokenMul
           | TokenLParen
           | TokenRParen
	   | TokenNL
	   | TokenConstr String
	   | TokenSig
	   | TokenBoxLeft
	   | TokenBoxRight
	   | TokenLBrace
	   | TokenRBrace
	   | TokenLangle
	   | TokenRangle
	   | TokenComma
	   | TokenPipe
	   | TokenUnderscore
	   | TokenSemicolon
           deriving (Eq,Show)

scanTokens = trim . alexScanTokens

trim :: [Token] -> [Token]
trim = reverse . trimNL . reverse . trimNL

trimNL :: [Token] -> [Token]
trimNL [] = []
trimNL (TokenNL : ts) = trimNL ts
trimNL ts = ts 



}
