{
module Syntax.Parser where

import Syntax.Lexer
import Syntax.Expr
import Syntax.Desugar
import Numeric

}

%name defs
%tokentype { Token }
%error { parseError }

%token
    nl    { TokenNL }
    let   { TokenLet }
    in    { TokenIn }
    case  { TokenCase }
    of    { TokenOf }
    INT   { TokenInt $$ }
    REAL  { TokenFloat $$ }
    VAR   { TokenSym $$ }
    CONSTR { TokenConstr $$ }
    forall { TokenForall }
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
    '_'   { TokenUnderscore }
    ';'   { TokenSemicolon }
    '.'   { TokenPeriod }


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

Sig ::  { (String, TypeScheme) }
Sig : VAR ':' TypeScheme           { ($1, $3) }

Binding :: { (String, Expr, [Pattern]) }
Binding : VAR '=' Expr             { ($1, $3, []) }
        | VAR Pats '=' Expr        { ($1, $4, $2) }

Pats :: { [Pattern] }
Pats : Pat                         { [$1] }
     | Pat Pats                    { $1 : $2 }

Pat :: { Pattern }
Pat : VAR                          { PVar $1 }
    | '_'                          { PWild }
    | '|' VAR '|'                  { PBoxVar $2 }
    | INT                          { PInt $1 }
    | REAL                         { PFloat $ read $1 }
    | CONSTR                       { PConstr $1 }

TypeScheme :: { TypeScheme }
TypeScheme :
    Type                             { Forall [] $1 }
  | forall '(' CKinds ')' '.' Type   { Forall $3 $6 }
  | forall CKinds '.' Type           { Forall $2 $4 }


CKinds :: { [(String, CKind)] }
CKinds :
   CKindSig ',' CKinds { $1 : $3 }
 | CKindSig            { [$1] }

CKindSig :: { (String, CKind) }
CKindSig :
    VAR ':' CKind { ($1, $3) }
  | VAR           { ($1, CPoly "") }

CKind :: { CKind }
CKind :
    VAR     { CPoly $1 }
  | CONSTR  { CConstr $1 }


Type :: { Type }
Type :
       CONSTR                      { ConT $1 }
     | Type '->' Type              { FunTy $1 $3 }
     | Type '|' Coeffect '|'       { Box $3 $1 }
     | '(' Type ')'                { $2 }
     | '<' Type '>' Effect         { Diamond $4 $2 }
     | VAR                         { TyVar $1 }

Coeffect :: { Coeffect }
Coeffect :
       NatCoeff                { $1 }
     | '*'                     { CNatOmega (Left ()) }
     | REAL                    { CFloat $ myReadFloat $1 }
     | CONSTR                  { case $1 of
                                   "Lo" -> Level 0
                                   "Hi" -> Level 1 }
     | VAR                     { CVar $1 }
     | Coeffect '+' Coeffect   { CPlus $1 $3 }
     | Coeffect '*' Coeffect   { CTimes $1 $3 }
     | '(' Coeffect ')'        { $2 }
     | '{' Set '}'             { CSet $2 }

NatCoeff :: { Coeffect }
NatCoeff : INT NatModifier              { CNat $2 $1 }

NatModifier :: { NatModifier }
NatModifier : {- empty -}    { Ordered }
             | '='           { Discrete }

Set :: { [(String, Type)] }
Set :
    VAR ':' Type ',' Set   { ($1, $3) : $5 }
  | VAR ':' Type           { [($1, $3)] }

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
     CONSTR                     { $1 }

Expr :: { Expr }
Expr : let VAR ':' Type '=' Expr in Expr
                                   { App (Val (Abs $2 (Just $4) $8)) $6 }
     | let VAR '=' Expr in Expr
                                   { App (Val (Abs $2 Nothing $6)) $4 }

     | let '|' VAR ':' Type '|' CKind '=' Expr in Expr
                                   { LetBox $3 $5 $7 $9 $11 }
     | '\\' '(' VAR ':' Type ')' '->' Expr
                                   { Val (Abs $3 (Just $5) $8) }

     | '\\' VAR '->' Expr          { Val (Abs $2 Nothing $4) }


     | let '<' VAR ':' Type '>' '=' Expr in Expr
                                   { LetDiamond $3 $5 $8 $10 }
     | '<' Expr '>'                { Val (Pure $2) }
     | Form                        { $1 }
     | case Expr of Cases          { Case $2 $4 }

Cases :: { [(Pattern, Expr)] }
Cases : Case CasesNext { $1 : $2 }

CasesNext :: { [(Pattern, Expr)] }
CasesNext : ';' Cases    { $2 }
          | {- empty -}  { [] }

Case :: { (Pattern, Expr) }
Case : Pat '->' Expr { ($1, $3) }

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
     | INT                         { Val $ NumInt $1 }
     | REAL                        { Val $ NumFloat $ read $1 }
     | VAR                         { Val $ Var $1 }
     | '|' Atom '|'                { Val $ Promote $2 }
     | CONSTR                      { Val $ Constr $1 }


{

parseError :: [Token] -> a
parseError t = error $ "Parse error, at token " ++ show t

parseDefs :: String -> ([Def], [(Id, Id)])
parseDefs = uniqueNames . map desugar . defs . scanTokens

myReadFloat :: String -> Rational
myReadFloat str =
    case readFloat str of
      ((n, []):_) -> n
      _ -> error "Invalid number"

fst3 (a, b, c) = a
snd3 (a, b, c) = b
thd3 (a, b, c) = c
}
