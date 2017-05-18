{
module HappyParser where

import AlexToken
import Expr
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
    '\\'  { TokenLambda }
    '->'  { TokenArrow }
    '='   { TokenEq }
    '+'   { TokenAdd }
    '-'   { TokenSub }
    '*'   { TokenMul }
    '('   { TokenLParen }
    ')'   { TokenRParen }

%left '+' '-'
%left '*'
%%

Defs : Def                         { [$1] }
     | Defs nl Def                 { $1 ++ [$3] }

Def : VAR '=' Expr                 { Def $1 $3 }

Expr : let VAR '=' Expr in Expr    { App (Abs $2 $6) $4 }
     | '\\' VAR '->' Expr          { Abs $2 $4 }
     | Form                        { $1 }

Form : Form '+' Form               { Binop Add $1 $3 }
     | Form '-' Form               { Binop Sub $1 $3 }
     | Form '*' Form               { Binop Mul $1 $3 }
     | Juxt                        { $1 }

Juxt : Juxt Atom                   { App $1 $2 }
     | Atom                        { $1 }

Atom : '(' Expr ')'                { $2 }
     | NUM                         { Num $1 }
     | VAR                         { Var $1 }

{
parseError :: [Token] -> a
parseError t = error $ "Parse error, at token " ++ show t

parseDefs :: String -> [Def]
parseDefs = defs . scanTokens
}
