{
module Syntax.Parser where

import Syntax.Lexer
import Syntax.Expr
}

%name defs
%tokentype { Token }
%error { parseError }

%token
    nl    { TokenNL }
    let   { TokenLet }
    in    { TokenIn }
    NUM   { TokenNum $$ }
    VAR   { TokenSym $$ }
    Int   { TokenInt }
    Bool  { TokenBool }
    '\\'  { TokenLambda }
    '->'  { TokenArrow }
    ','   { TokenComma }
    '='   { TokenEq }
    '+'   { TokenAdd }
    '-'   { TokenSub }
    '*'   { TokenMul }
    '('   { TokenLParen }
    ')'   { TokenRParen }
    ':'   { TokenSig }
    '['   { TokenBoxLeft }
    '{'   { TokenLBrace }
    '}'   { TokenRBrace }
    ']'   { TokenBoxRight }
    '<'   { TokenLangle }
    '>'   { TokenRangle }
    '|'   { TokenPipe }


%right in
%right '->'
%left '+' '-'
%left '*'
%left '|'
%left '.'
%%

Defs :: { [Def] }
Defs : Def                      { [$1] }
     | Def NL Defs              { $1 : $3 }

NL : nl NL {}
   | nl    {}

Def :: { Def }
Def : Sig nl Binding            { if (fst $1 == fst3 $3)
	                           then Def (fst3 $3) (snd3 $3) (thd3 $3) (snd $1)
 	                           else error $ "Signature for " ++ fst3 $3 ++ " does not match the signature head" }

Sig ::  { (String, Type) }
Sig : VAR ':' Type                 { ($1, $3) }

Binding :: { (String, Expr, [Either String String]) }
Binding : VAR '=' Expr             { ($1, $3, []) }
        | VAR Pats '=' Expr        { ($1, $4, $2) }

Pats :: { [Either String String] }
Pats : Pat                         { [$1] }
     | Pat Pats                    { $1 : $2 }

Pat :: { Either String String }
Pat : VAR                          { Left $1 }
    | '|' VAR '|'                  { Right $2 }

Type :: { Type }
Type : Int                         { ConT TyInt }
     | Bool                        { ConT TyBool }
     | Type '->' Type              { FunTy $1 $3 }
     | '|' Type '|' Coeffect       { Box $4 $2 }
     | '(' Type ')'                { $2 }
     | '<' Type '>' Effect         { Diamond $4 $2 }

Coeffect :: { Coeffect }
Coeffect :
       NUM                     { Nat $1 }
     | VAR                     { case $1 of
                                   "Lo" -> Level 0
                                   "Hi" -> Level 1
                                   c    -> CVar c }
     | Coeffect '+' Coeffect   { CPlus $1 $3 }
     | Coeffect '*' Coeffect   { CTimes $1 $3 }
     | '(' Coeffect ')'        { $2 }

Effect :: { Effect }
Effect :
     '[' Effs ']'             { $2 }
   | '[' ']'                  { [] }

Effs :: { [String] }
Effs :
     Eff ',' Effs            { $1 : $3 }
   | Eff                     { [$1] }

Eff :: { String }
Eff :
     VAR                     { $1 }

Expr :: { Expr }
Expr : let VAR '=' Expr in Expr    { App (Abs $2 $6) $4 }
     | let '|' VAR ':' Type '|' '=' Expr in Expr
                                   { LetBox $3 $5 $8 $10 }
     | '\\' VAR '->' Expr          { Abs $2 $4 }
     | let '<' VAR ':' Type '>' '=' Expr in Expr
                                   { LetDiamond $3 $5 $8 $10 }
     | '<' Expr '>'                { Pure $2 }
     | Form                        { $1 }

Form :: { Expr }
Form : Form '+' Form               { Binop Add $1 $3 }
     | Form '-' Form               { Binop Sub $1 $3 }
     | Form '*' Form               { Binop Mul $1 $3 }
     | Juxt                        { $1 }

Juxt :: { Expr }
Juxt : Juxt Atom                   { App $1 $2 }
     | Atom                        { $1 }

Atom :: { Expr }
Atom : '(' Expr ')'                { $2 }
     | NUM                         { Num $1 }
     | VAR                         { Var $1 }
     | '|' Atom '|'                { Promote $2 }


{
parseError :: [Token] -> a
parseError t = error $ "Parse error, at token " ++ show t

parseDefs :: String -> ([Def], [(Id, Id)])
parseDefs = uniqueNames . map desugar . defs . scanTokens
}
