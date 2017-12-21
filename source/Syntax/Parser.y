{
module Syntax.Parser where

import Syntax.Lexer
import Syntax.Expr

import Control.Monad (forM)
import Data.List ((\\), intercalate, nub, stripPrefix)
import Data.Maybe (catMaybes)
import Numeric
import System.Exit (die)

}

%name defs
%tokentype { Token }
%error { parseError }
%monad { IO }

%token
    nl    { TokenNL  _ }
    let   { TokenLet _ }
    in    { TokenIn  _  }
    case  { TokenCase _ }
    of    { TokenOf _ }
    INT   { TokenInt _ _ }
    FLOAT  { TokenFloat _ _}
    VAR    { TokenSym _ _ }
    CONSTR { TokenConstr _ _ }
    forall { TokenForall _ }
    '∞'   { TokenInfinity _ }
    '\\'  { TokenLambda _ }
    '/'  { TokenForwardSlash _ }
    '->'  { TokenArrow _ }
    '<-'  { TokenBind _ }
    ','   { TokenComma _ }
    '='   { TokenEq _ }
    '+'   { TokenAdd _ }
    '-'   { TokenSub _ }
    '*'   { TokenMul _ }
    '('   { TokenLParen _ }
    ')'   { TokenRParen _ }
    ':'   { TokenSig _ }
    '['   { TokenBoxLeft _ }
    '{'   { TokenLBrace _ }
    '}'   { TokenRBrace _ }
    ']'   { TokenBoxRight _ }
    '<'   { TokenLangle _ }
    '>'   { TokenRangle _ }
    '|'   { TokenPipe _ }
    '_'   { TokenUnderscore _ }
    ';'   { TokenSemicolon _ }
    '.'   { TokenPeriod _ }
    OP    { TokenOp _ _ }


%right in
%right '->'
%left ':'
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
Def : Sig NL Binding
  { if (fst3 $1 == fst3 $3)
    then Def (thd3 $1, getEnd $ snd3 $3) (fst3 $3) (snd3 $3) (thd3 $3) (snd3 $1)
    else error $ "Signature for "
	            ++ fst3 $3
	            ++ " does not match the signature head" }

Sig ::  { (String, TypeScheme, Pos) }
Sig : VAR ':' TypeScheme           { (symString $1, $3, getPos $1) }

Binding :: { (String, Expr, [Pattern]) }
Binding : VAR '=' Expr             { (symString $1, $3, []) }
        | VAR Pats '=' Expr        { (symString $1, $4, $2) }

Pats :: { [Pattern] }
Pats : Pat                         { [$1] }
     | Pat Pats                    { $1 : $2 }

Pat :: { Pattern }
Pat :
    '(' Pat ',' Pat ')'            { PPair (getPosToSpan $1) $2 $4 }
  | '|' Pat '|'                    { PBox (getPosToSpan $1) $2 }
  | PAtom                          { $1 }

PJuxt :: { Pattern }
PJuxt :
    PJuxt PAtom                    { PApp (getStart $1, getEnd $2) $1 $2 }
  | PAtom                          { $1 }


PAtom :: { Pattern }
PAtom : VAR                        { PVar (getPosToSpan $1) (symString $1) }
    | '_'                          { PWild (getPosToSpan $1) }
    | INT                          { let TokenInt _ x = $1
	                             in PInt (getPosToSpan $1) x }
    | FLOAT                        { let TokenFloat _ x = $1
	                             in PFloat (getPosToSpan $1) $ read x }
    | CONSTR                       { let TokenConstr _ x = $1
	                             in PConstr (getPosToSpan $1) x }
    | '(' PJuxt ')'                  { $2 }

TypeScheme :: { TypeScheme }
TypeScheme :
   Type                             { Forall nullSpan [] $1 }
 | forall '(' VarSigs ')' '.' Type   { Forall (getPos $1, getPos $5) $3 $6 }
 | forall VarSigs '.' Type           { Forall (getPos $1, getPos $3) $2 $4 }


VarSigs :: { [(String, Kind)] }
VarSigs :
   VarSig ',' VarSigs { $1 : $3 }
 | VarSig             { [$1] }

VarSig :: { (String, Kind) }
VarSig :
    VAR ':' Kind { (symString $1, $3) }

Kind :: { Kind }
Kind :
    VAR     { KPoly (symString $1) }
  | CONSTR  { case constrString $1 of
                "Type"     -> KType
                "Coeffect" -> KCoeffect
                s          -> KConstr s }

CKind :: { CKind }
CKind :
   VAR     { CPoly (symString $1) }
 | CONSTR  { CConstr (constrString $1) }

Type :: { Type }
Type :
    TyJuxt                       { $1 }
  | Type '->' Type               { FunTy $1 $3 }
  | Type '|' Coeffect '|'        { Box $3 $1 }
  | Type '<' Effect '>'          { Diamond $3 $1 }
  | '(' Type ')'                 { $2 }
  | '(' Type ',' Type ')'        { PairTy $2 $4 }

TyJuxt :: { Type }
TyJuxt :
    TyJuxt TyAtom               { TyApp $1 $2 }
  | TyAtom                      { $1 }

TyAtom :: { Type }
TyAtom :
    CONSTR                      { TyCon $ constrString $1 }
  | VAR                         { TyVar (symString $1) }
  | INT                         { let TokenInt _ x = $1 in TyInt x }
  | TyAtom '+' TyAtom           { TyInfix ("+") $1 $3 }
  | TyAtom '*' TyAtom           { TyInfix ("*") $1 $3 }
  | TyAtom '/' '\\' TyAtom      { TyInfix ("/\\") $1 $4 }
  | TyAtom '\\' '/' TyAtom      { TyInfix ("\\/") $1 $4 }
  | '(' Type '|' Coeffect '|' ')' { Box $4 $2 }
  | '(' TyAtom ')' { $2 }

Coeffect :: { Coeffect }
Coeffect :
       NatCoeff                { $1 }
     | '∞'                     { CInfinity (CPoly " infinity") }
     | FLOAT                   { let TokenFloat _ x = $1
                                 in CFloat $ myReadFloat x }
     | CONSTR                  { case (constrString $1) of
                                   "Lo" -> Level 0
                                   "Hi" -> Level 1
                                   "Inf" -> CInfinity (CPoly " infinity")
                               }
     | VAR                     { CVar (symString $1) }
     | Coeffect '+' Coeffect   { CPlus $1 $3 }
     | Coeffect '*' Coeffect   { CTimes $1 $3 }
     | Coeffect '/' '\\' Coeffect { CMeet $1 $4 }
     | Coeffect '\\' '/' Coeffect { CJoin $1 $4 }
     | '(' Coeffect ')'        { $2 }
     | '{' Set '}'             { CSet $2 }
     | Coeffect ':' CKind      { normalise (CSig $1 $3) }

NatCoeff :: { Coeffect }
NatCoeff : INT NatModifier     { let TokenInt _ x = $1
                                 in CNat $2 x }

NatModifier :: { NatModifier }
NatModifier : {- empty -}    { Ordered }
             | '='           { Discrete }

Set :: { [(String, Type)] }
Set :
    VAR ':' Type ',' Set   { (symString $1, $3) : $5 }
  | VAR ':' Type           { [(symString $1, $3)] }

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
     CONSTR                     { constrString $1 }

Expr :: { Expr }
Expr : let VAR ':' Type '=' Expr in Expr
         { App (getPos $1, getEnd $8) (Val (getSpan $6) (Abs (symString $2) (Just $4) $8)) $6 }

     | let VAR '=' Expr in Expr
         { App (getPos $1, getEnd $6) (Val (getSpan $6) (Abs (symString $2) Nothing $6)) $4 }

     | let '|' VAR '|' ':' Type '=' Expr in Expr
         { LetBox (getPos $1, getEnd $10) (symString $3) $6 $8 $10 }

     | '\\' '(' VAR ':' Type ')' '->' Expr
         { Val (getPos $1, getEnd $8) (Abs (symString $3) (Just $5) $8) }

     | '\\' VAR '->' Expr
         { Val (getPos $1, getEnd $4) (Abs (symString $2) Nothing $4) }

     | let VAR ':' Type '<-' Expr in Expr
         { LetDiamond (getPos $1, getEnd $8) (symString $2) $4 $6 $8 }

     | case Expr of Cases
        { Case (getPos $1, getEnd . snd . last $ $4) $2 $4 }

     | Form
        { $1 }

Cases :: { [(Pattern, Expr)] }
Cases : Case CasesNext { $1 : $2 }

CasesNext :: { [(Pattern, Expr)] }
CasesNext : ';' Cases    { $2 }
          | {- empty -}  { [] }

Case :: { (Pattern, Expr) }
Case : Pat '->' Expr { ($1, $3) }

Form :: { Expr }
Form : Form '+' Form               { Binop (getPosToSpan $2) "+" $1 $3 }
     | Form '-' Form               { Binop (getPosToSpan $2) "-" $1 $3 }
     | Form '*' Form               { Binop (getPosToSpan $2) "*" $1 $3 }
     | Form '<' Form               { Binop (getPosToSpan $2) "<" $1 $3 }
     | Form '>' Form               { Binop (getPosToSpan $2) ">" $1 $3 }
     | Form OP  Form               { Binop (getPosToSpan $2) (symString $2) $1 $3 }
     | Juxt                        { $1 }

Juxt :: { Expr }
Juxt : Juxt Atom                   { App (getStart $1, getEnd $2) $1 $2 }
     | Atom                        { $1 }

Atom :: { Expr }
Atom : '(' Expr ')'                { $2 }
     | INT     { let (TokenInt _ x) = $1
                 in Val (getPosToSpan $1) $ NumInt x }

     | FLOAT   { let (TokenFloat _ x) = $1
                 in Val (getPosToSpan $1) $ NumFloat $ read x }

     | VAR     { Val (getPosToSpan $1) $ Var (symString $1) }

     | '|' Atom '|'
               { Val (getPos $1, getPos $3) $ Promote $2 }

     | CONSTR  { Val (getPosToSpan $1) $ Constr (constrString $1) [] }

     | '(' Expr ',' Expr ')'
        { Val (getPos $1, getPos $5) (Pair $2 $4) }

{

parseError :: [Token] -> IO a
parseError [] = do
    die "Premature end of file"
parseError t = do
    die $ show l ++ ":" ++ show c ++ ": parse error"
  where (l, c) = getPos (head t)

parseDefs :: String -> IO ([Def], [(Id, Id)])
parseDefs input = do
    defs <- parse input
    importedDefs <- forM imports $ \path -> do
      src <- readFile path
      parseDefs src
    checkNameClashes $ push $ importedDefs ++ [defs] -- add defs at the end because definitions
                                                     -- need to precede use sites
  where
    parse = fmap (uniqueNames . freshenBlankPolyVars) . defs . scanTokens
    imports = map ((++ ".gr") . replace '.' '/') . catMaybes . map (stripPrefix "import ") . lines $ input
    push ps = (concatMap fst ps, concatMap snd ps)
    replace from to = map (\c -> if c == from then to else c)
    checkNameClashes ds =
        if null clashes then return ds
        else die $ "Error: Name clash: " ++ intercalate ", " clashes
      where
        clashes = names \\ nub names
        names = map (\(Def _ name _ _ _) -> name) (fst ds)

myReadFloat :: String -> Rational
myReadFloat str =
    case readFloat str of
      ((n, []):_) -> n
      _ -> error "Invalid number"

fst3 (a, b, c) = a
snd3 (a, b, c) = b
thd3 (a, b, c) = c
}
