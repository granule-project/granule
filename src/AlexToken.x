{
{-# OPTIONS_GHC -w #-}
module AlexToken (Token(..),scanTokens) where
import Expr
import Debug.Trace
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$eol   = [\n]

tokens :-

  $eol+                         { \s -> TokenNL }
  $white+                       ;
  "#".*                         ;
  let                           { \s -> TokenLet }
  in                            { \s -> TokenIn }
  $digit+                       { \s -> TokenNum (read s) }
  "->"                          { \s -> TokenArrow }
  \=                            { \s -> TokenEq }
  \\                            { \s -> TokenLambda }
  [\+]                          { \s -> TokenAdd }
  [\-]                          { \s -> TokenSub }
  [\*]                          { \s -> TokenMul }
  \(                            { \s -> TokenLParen }
  \)                            { \s -> TokenRParen }
  $alpha [$alpha $digit \_ \']* { \s -> TokenSym s }

{

data Token = TokenLet
           | TokenIn
           | TokenLambda
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
           deriving (Eq,Show)

scanTokens = trim . alexScanTokens

trim :: [Token] -> [Token]
trim = reverse . trimNL . reverse . trimNL

trimNL :: [Token] -> [Token]
trimNL [] = []
trimNL (TokenNL : ts) = trimNL ts
trimNL ts = ts 



}
