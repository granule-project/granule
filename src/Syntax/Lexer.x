{
{-# OPTIONS_GHC -w #-}
module Syntax.Lexer (Token(..),scanTokens) where
import Syntax.Expr
import Debug.Trace
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$eol   = [\n]

tokens :-

  $eol+                         { \s -> TokenNL }
  $white+                       ;
  "--".*                         ;
  Int                           { \s -> TokenInt }
  Bool                          { \s -> TokenBool }
  let                           { \s -> TokenLet }
  in                            { \s -> TokenIn }
  $digit+                       { \s -> TokenNum (read s) }
  "->"                          { \s -> TokenArrow }
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
  $alpha [$alpha $digit \_ \']* { \s -> TokenSym s }
  \_                            { \_ -> TokenUnderscore }
  \|                            { \s -> TokenPipe }

{

data Token = TokenLet
           | TokenIn
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
	   | TokenInt
	   | TokenBool
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
           deriving (Eq,Show)

scanTokens = trim . alexScanTokens

trim :: [Token] -> [Token]
trim = reverse . trimNL . reverse . trimNL

trimNL :: [Token] -> [Token]
trimNL [] = []
trimNL (TokenNL : ts) = trimNL ts
trimNL ts = ts 



}
