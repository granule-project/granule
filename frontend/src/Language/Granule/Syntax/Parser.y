{
{-# LANGUAGE ImplicitParams #-}
module Language.Granule.Syntax.Parser where

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Lexer
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Utils

import Control.Monad (forM)
import Data.List ((\\), intercalate, nub, stripPrefix)
import Data.Maybe (mapMaybe)
import Numeric
import System.Exit (die)

}

%name defs Defs
%name expr Expr
%name tscheme TypeScheme
%tokentype { Token }
%error { parseError }
%monad { IO }

%token
    nl    { TokenNL  _ }
    data  { TokenData _ }
    where { TokenWhere _ }
    let   { TokenLet _ }
    in    { TokenIn  _  }
    if    { TokenIf _ }
    then  { TokenThen _ }
    else  { TokenElse _ }
    case  { TokenCase _ }
    of    { TokenOf _ }
    INT   { TokenInt _ _ }
    FLOAT  { TokenFloat _ _}
    VAR    { TokenSym _ _ }
    CONSTR { TokenConstr _ _ }
    CHAR   { TokenCharLiteral _ _ }
    STRING { TokenStringLiteral _ _ }
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
    '`'   { TokenBackTick _ }
    '^'   { TokenCaret _ }
    ".."  { TokenDotDot _ }
    OP    { TokenOp _ _ }


%right in
%right '->'
%left ':'
%left '+' '-'
%left '*'
%left '^'
%left '|'
%left '.'
%%

Defs :: { AST () () }
  : Def                       { AST [] [$1] }

  | DataDecl                  { AST [$1] [] }

  | DataDecl NL Defs          { let (AST dds defs) = $3
                                 in AST ($1 : dds) defs }
  | Def NL Defs               { let (AST dds defs) = $3
                                 in AST dds ($1 : defs) }

NL :: { () }
NL : nl NL                    { }
   | nl                       { }

Def :: { Def () () }
  : Sig NL Binding
      { if (fst3 $1 == fst3 $3)
        then Def (thd3 $1, getEnd $ snd3 $3) (fst3 $3) (snd3 $3) (thd3 $3) (snd3 $1)
        else error $ "Signature for `" <> sourceName (fst3 $3) <> "` does not match the \
                                      \signature head `" <> sourceName (fst3 $1) <> "`"  }

DataDecl :: { DataDecl }
  : data CONSTR TyVars KindAnn where DataConstrs
      { DataDecl (getPos $1, snd $ getSpan (last $6)) (mkId $ constrString $2) $3 $4 $6 }

Sig ::  { (Id, TypeScheme, Pos) }
  : VAR ':' TypeScheme        { (mkId $ symString $1, $3, getPos $1) }

Binding :: { (Id, Expr () (), [Pattern ()]) }
  : VAR '=' Expr              { (mkId $ symString $1, $3, []) }
  | VAR Pats '=' Expr         { (mkId $ symString $1, $4, $2) }

DataConstrs :: { [DataConstr] }
  : DataConstr DataConstrNext { $1 : $2 }
  | {- empty -}               { [] }

DataConstr :: { DataConstr }
  : CONSTR ':' TypeScheme     { DataConstrG (getPos $1, getEnd $3) (mkId $ constrString $1) $3 }
  | CONSTR TyParams           { DataConstrA (getPosToSpan $1) (mkId $ constrString $1) $2 }

DataConstrNext :: { [DataConstr] }
  : ';' DataConstrs           { $2 }
  | {- empty -}               { [] }

TyVars :: { [(Id, Kind)] }
  : '(' VAR ':' Kind ')' TyVars { (mkId $ symString $2, $4) : $6 }
  | VAR TyVars                  { (mkId $ symString $1, KType) : $2 }
  | {- empty -}                 { [] }

KindAnn :: { Maybe Kind }
  : ':' Kind                  { Just $2 }
  | {- empty -}               { Nothing }

Pats :: { [Pattern ()] }
  : Pat                       { [$1] }
  | Pat Pats                  { $1 : $2 }

PAtoms :: { [Pattern ()] }
  : PAtom                     { [$1] }
  | PAtom PAtoms              { $1 : $2 }

Pat :: { Pattern () }
  : PAtom                     { $1 }

PatNested :: { Pattern () }
PatNested
 : '(' CONSTR PAtoms ')'     { let TokenConstr _ x = $2 in PConstr (getPosToSpan $2) () (mkId x) $3 }

PAtom :: { Pattern () }
  : VAR                       { PVar (getPosToSpan $1) () (mkId $ symString $1) }
  | '_'                       { PWild (getPosToSpan $1) () }
  | INT                       { let TokenInt _ x = $1 in PInt (getPosToSpan $1) () x }
  | FLOAT                     { let TokenFloat _ x = $1 in PFloat (getPosToSpan $1) () $ read x }
  | CONSTR                    { let TokenConstr _ x = $1 in PConstr (getPosToSpan $1) () (mkId x) [] }
  | PatNested                 { $1 }
  | '|' Pat '|'               { PBox (getPosToSpan $1) () $2 }
  | '(' Pat ',' Pat ')'       { PConstr (getPosToSpan $1) () (mkId ",") [$2, $4] }


TypeScheme :: { TypeScheme }
  : Type                              { Forall nullSpan [] $1 }
  | forall '(' VarSigs ')' '.' Type   { Forall (getPos $1, getPos $5) $3 $6 }
  | forall VarSigs '.' Type           { Forall (getPos $1, getPos $3) $2 $4 }

VarSigs :: { [(Id, Kind)] }
  : VarSig ',' VarSigs        { $1 : $3 }
  | VarSig                    { [$1] }

VarSig :: { (Id, Kind) }
  : VAR ':' Kind              { (mkId $ symString $1, $3) }

Kind :: { Kind }
  : Kind '->' Kind            { KFun $1 $3 }
  | VAR                       { KVar (mkId $ symString $1) }
  | CONSTR                    { case constrString $1 of
                                  "Type"     -> KType
                                  "Coeffect" -> KCoeffect
                                  s          -> KConstr $ mkId s }
Type :: { Type }
  : TyJuxt                    { $1 }
  | Type '->' Type            { FunTy $1 $3 }
  | TyAtom '|' Coeffect '|'   { Box $3 $1 }
  | TyAtom '<' Effect '>'     { Diamond $3 $1 }

TyJuxt :: { Type }
  : TyJuxt '`' TyAtom '`'     { TyApp $3 $1 }
  | TyJuxt TyAtom             { TyApp $1 $2 }
  | TyAtom                    { $1 }
  | TyAtom '+' TyAtom         { TyInfix ("+") $1 $3 }
  | TyAtom '*' TyAtom         { TyInfix ("*") $1 $3 }
  | TyAtom '^' TyAtom         { TyInfix ("^") $1 $3 }
  | TyAtom '/' '\\' TyAtom    { TyInfix ("/\\") $1 $4 }
  | TyAtom '\\' '/' TyAtom    { TyInfix ("\\/") $1 $4 }

TyAtom :: { Type }
  : CONSTR                    { TyCon $ mkId $ constrString $1 }
  | VAR                       { TyVar (mkId $ symString $1) }
  | INT                       { let TokenInt _ x = $1 in TyInt x }
  | '(' Type ')'              { $2 }
  | '(' Type ',' Type ')'     { TyApp (TyApp (TyCon $ mkId ",") $2) $4 }

TyParams :: { [Type] }
  : TyAtom TyParams           { $1 : $2 } -- use right recursion for simplicity -- VBL
  |                           { [] }

Coeffect :: { Coeffect }
  : INT                         { let TokenInt _ x = $1 in CNat x }
  | '∞'                         { CInfinity Nothing }
  | FLOAT                       { let TokenFloat _ x = $1 in CFloat $ myReadFloat x }
  | CONSTR                      { case (constrString $1) of
                                    "Public" -> Level 0
                                    "Private" -> Level 1
                                    "Inf" -> CInfinity (TyCon $ mkId "Cartesian")
                                    x -> error $ "Unknown coeffect constructor `" <> x <> "`" }
  | VAR                         { CVar (mkId $ symString $1) }
  | Coeffect ".." Coeffect      { CUsage $1 $3 }
  | Coeffect '+' Coeffect       { CPlus $1 $3 }
  | Coeffect '*' Coeffect       { CTimes $1 $3 }
  | Coeffect '^' Coeffect       { CExpon $1 $3 }
  | Coeffect '/' '\\' Coeffect  { CMeet $1 $4 }
  | Coeffect '\\' '/' Coeffect  { CJoin $1 $4 }
  | '(' Coeffect ')'            { $2 }
  | '{' Set '}'                 { CSet $2 }
  | Coeffect ':' TyAtom         { normalise (CSig $1 $3) }

Set :: { [(String, Type)] }
  : VAR ':' Type ',' Set      { (symString $1, $3) : $5 }
  | VAR ':' Type              { [(symString $1, $3)] }

Effect :: { Effect }
  : '[' Effs ']'              { $2 }
  | '[' ']'                   { [] }

Effs :: { [String] }
  : Eff ',' Effs              { $1 : $3 }
  | Eff                       { [$1] }

Eff :: { String }
  : CONSTR                    { constrString $1 }

Expr :: { Expr () () }
  : let LetBind MultiLet
    { let (_, pat, mt, expr) = $2
	in App (getPos $1, getEnd $3) ()
	(Val (getSpan $3) () (Abs () pat mt $3)) expr }

  | '\\' '(' Pat ':' Type ')' '->' Expr
  { Val (getPos $1, getEnd $8) () (Abs () $3 (Just $5) $8) }

  | '\\' Pat '->' Expr
  { Val (getPos $1, getEnd $4) () (Abs () $2 Nothing $4) }

  | let LetBindEff MultiLetEff
      { let (_, pat, mt, expr) = $2
        in LetDiamond (getPos $1, getEnd $3) () pat mt expr $3 }

  | case Expr of Cases
  { Case (getPos $1, getEnd . snd . last $ $4) () $2 $4 }

  | if Expr then Expr else Expr
  { Case (getPos $1, getEnd $6) () $2 [(PConstr (getPosToSpan $3) () (mkId "True") [], $4),
                                       (PConstr (getPosToSpan $3) () (mkId "False") [], $6)] }

  | Form
    { $1 }

LetBind :: { (Pos, Pattern (), Maybe Type, Expr () ()) }
LetBind
 : Pat ':' Type '=' Expr
    { (getStart $1, $1, Just $3, $5) }
 | Pat '=' Expr
    { (getStart $1, $1, Nothing, $3) }

MultiLet :: { Expr () () }
MultiLet
  : ';' LetBind MultiLet
    { let (_, pat, mt, expr) = $2
	in App (getPos $1, getEnd $3) ()
     	    (Val (getSpan $3) () (Abs () pat mt $3)) expr }
  | in Expr
    { $2 }

LetBindEff :: { (Pos, Pattern (), Maybe Type, Expr () ()) }
LetBindEff :
   Pat '<-' Expr            { (getStart $1, $1, Nothing, $3) }
 | Pat ':' Type '<-' Expr   { (getStart $1, $1, Just $3, $5) }

MultiLetEff :: { Expr () () }
MultiLetEff
  : ';' LetBindEff MultiLetEff
      { let (_, pat, mt, expr) = $2
	  in LetDiamond (getPos $1, getEnd $3) () pat mt expr $3 }
  | in Expr
      { $2 }

Cases :: { [(Pattern (), Expr () () )] }
 : Case CasesNext             { $1 : $2 }

CasesNext :: { [(Pattern (), Expr () ())] }
  : ';' Cases                 { $2 }
  | {- empty -}               { [] }

Case :: { (Pattern (), Expr () ()) }
  : Pat '->' Expr             { ($1, $3) }
  | CONSTR PAtoms '->' Expr   { let TokenConstr _ x = $1
                                 in (PConstr (getPosToSpan $1) () (mkId x) $2, $4) }


Form :: { Expr () () }
  : Form '+' Form  { Binop (getPosToSpan $2) () "+" $1 $3 }
  | Form '-' Form  { Binop (getPosToSpan $2) () "-" $1 $3 }
  | Form '*' Form  { Binop (getPosToSpan $2) () "*" $1 $3 }
  | Form '<' Form  { Binop (getPosToSpan $2) () "<" $1 $3 }
  | Form '>' Form  { Binop (getPosToSpan $2) () ">" $1 $3 }
  | Form OP  Form  { Binop (getPosToSpan $2) () (symString $2) $1 $3 }
  | Juxt           { $1 }

Juxt :: { Expr () () }
  : Juxt '`' Atom '`'         { App (getStart $1, getEnd $3) () $3 $1 }
  | Juxt Atom                 { App (getStart $1, getEnd $2) () $1 $2 }
  | Atom                      { $1 }

Atom :: { Expr () () }
  : '(' Expr ')'              { $2 }
  | INT                       { let (TokenInt _ x) = $1
                                in Val (getPosToSpan $1) () $ NumInt x }
  | FLOAT                     { let (TokenFloat _ x) = $1
                                in Val (getPosToSpan $1) () $ NumFloat $ read x }
  | VAR                       { Val (getPosToSpan $1) () $ Var () (mkId $ symString $1) }
  | '|' Atom '|'              { Val (getPos $1, getPos $3) () $ Promote () $2 }
  | CONSTR                    { Val (getPosToSpan $1) () $ Constr () (mkId $ constrString $1) [] }
  | '(' Expr ',' Expr ')'     { App (getPos $1, getPos $5) ()
                                    (App (getPos $1, getPos $3) ()
                                         (Val (getPosToSpan $3) () (Constr () (mkId ",") []))
                                         $2)
                                    $4 }
  | CHAR                      { Val (getPosToSpan $1) () $
                                  case $1 of (TokenCharLiteral _ c) -> CharLiteral c }
  | STRING                    { Val (getPosToSpan $1) () $
                                  case $1 of (TokenStringLiteral _ c) -> StringLiteral c }

{
parseError :: [Token] -> IO a
parseError [] = do
    die "Premature end of file"
parseError t = do
    die $ show l <> ":" <> show c <> ": parse error"
  where (l, c) = getPos (head t)

parseDefs :: (?globals :: Globals) => String -> IO (AST () ())
parseDefs input = do
    ast <- parseDefs' input
    return $ freshenAST ast

parseDefs' :: (?globals :: Globals) => String -> IO (AST () ())
parseDefs' input = do
    defs <- parse input
    importedDefs <- forM imports $ \path -> do
      src <- readFile path
      let ?globals = ?globals { sourceFilePath = path }
      parseDefs' src
    let allDefs = merge $ defs : importedDefs
    checkNameClashes allDefs
    return allDefs

  where
    merge :: [AST () ()] -> AST () ()
    merge xs =
      let conc [] dds defs = AST dds defs
          conc ((AST dds defs):xs) ddsAcc defsAcc = conc xs (dds <> ddsAcc) (defs <> defsAcc)
       in conc xs [] []

    parse = defs . scanTokens

    imports = map (("StdLib/" <> ) . (<> ".gr") . replace '.' '/')
              . mapMaybe (stripPrefix "import ") . lines $ input

    replace from to = map (\c -> if c == from then to else c)

    checkNameClashes ds@(AST dataDecls defs) =
        if null clashes
	        then return ()
          else die $ "Error: Name clash: " <> intercalate ", " (map sourceName clashes)
      where
        clashes = names \\ nub names
        names = (`map` dataDecls) (\(DataDecl _ name _ _ _) -> name)
                <> (`map` defs) (\(Def _ name _ _ _) -> name)

myReadFloat :: String -> Rational
myReadFloat str =
    case readFloat str of
      ((n, []):_) -> n
      _ -> error "Invalid number"

fst3 (a, b, c) = a
snd3 (a, b, c) = b
thd3 (a, b, c) = c
}
