{
{-# LANGUAGE ImplicitParams #-}
module Syntax.Parser where

import Syntax.Lexer
import Syntax.Expr
import Utils

import Control.Monad (forM)
import Data.List ((\\), intercalate, nub, stripPrefix)
import Data.Maybe (catMaybes)
import Numeric
import System.Exit (die)

}

%name defs Defs
%name expr Expr
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
    OP    { TokenOp _ _ }


%right in
%right '->'
%left ':'
%left '+' '-'
%left '*'
%left '|'
%left '.'
%%

Defs :: { AST }
  : Def                       { [$1] }
  | Def NL Defs               { $1 : $3 }

NL : nl NL                    { }
   | nl                       { }

Def :: { Def }
  : Sig NL Binding
      { if (fst3 $1 == fst3 $3)
        then Def (thd3 $1, getEnd $ snd3 $3) (fst3 $3) (snd3 $3) (thd3 $3) (snd3 $1)
        else error $ "Signature for `" ++ sourceName (fst3 $3) ++ "` does not match the \
                                      \signature head `" ++ sourceName (fst3 $1) ++ "`"  }

  | data CONSTR TyVars KindAnn where DataConstrs
      { ADT (getPos $1, snd $ getSpan (last $6)) (mkId $ constrString $2) $3 $4 $6 }

Sig ::  { (Id, TypeScheme, Pos) }
  : VAR ':' TypeScheme        { (mkId $ symString $1, $3, getPos $1) }

Binding :: { (Id, Expr, [Pattern]) }
  : VAR '=' Expr              { (mkId $ symString $1, $3, []) }
  | VAR Pats '=' Expr         { (mkId $ symString $1, $4, $2) }

DataConstrs :: { [DataConstr] }
  : DataConstr DataConstrNext { $1 : $2 }

DataConstr :: { DataConstr }
  : CONSTR ':' TypeScheme     { DataConstr (getPos $1, getEnd $3) (mkId $ constrString $1) $3 }

DataConstrNext :: { [DataConstr] }
  : ';' DataConstrs           { $2 }
  | {- empty -}               { [] }

TyVars :: { [(Id,Kind)] }
  : '(' VAR ':' Kind ')' TyVars { (mkId $ symString $2, $4) : $6 }
  | VAR TyVars                  { (mkId $ symString $1, KType) : $2 }
  | {- empty -}                 { [] }

KindAnn :: { Maybe Kind }
  : ':' Kind                  { Just $2 }
  | {- empty -}               { Nothing }

Pats :: { [Pattern] }
  : Pat                       { [$1] }
  | Pat Pats                  { $1 : $2 }

PAtoms :: { [Pattern] }
  : PAtom                     { [$1] }
  | PAtom PAtoms              { $1 : $2 }

Pat :: { Pattern }
  : PAtom                     { $1 }
  | '(' CONSTR PAtoms ')'      { let TokenConstr _ x = $2 in PConstr (getPosToSpan $2) (mkId x) $3 }

PAtom :: { Pattern }
  : VAR                       { PVar (getPosToSpan $1) (mkId $ symString $1) }
  | '_'                       { PWild (getPosToSpan $1) }
  | INT                       { let TokenInt _ x = $1 in PInt (getPosToSpan $1) x }
  | FLOAT                     { let TokenFloat _ x = $1 in PFloat (getPosToSpan $1) $ read x }
  | CONSTR                    { let TokenConstr _ x = $1 in PConstr (getPosToSpan $1) (mkId x) [] }
  | '(' Pat ')'               { $2 }
  | '|' Pat '|'               { PBox (getPosToSpan $1) $2 }
  | '(' Pat ',' Pat ')'       { PPair (getPosToSpan $1) $2 $4 }


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
  | VAR                       { KPoly (mkId $ symString $1) }
  | CONSTR                    { case constrString $1 of
                                  "Type"     -> KType
                                  "Coeffect" -> KCoeffect
                                  s          -> KConstr $ mkId s }

CKind :: { CKind }
  : VAR                       { CPoly (mkId $ symString $1) }
  | CONSTR                    { CConstr (mkId $ constrString $1) }

Type :: { Type }
  : TyJuxt                    { $1 }
  | Type '->' Type            { FunTy $1 $3 }
  | Type '|' Coeffect '|'     { Box $3 $1 }
  | Type '<' Effect '>'       { Diamond $3 $1 }
  | '(' Type ')'              { $2 }
  | '(' Type ',' Type ')'     { PairTy $2 $4 }

TyJuxt :: { Type }
  : TyJuxt '`' TyAtom '`'     { TyApp $3 $1 }
  | TyJuxt TyAtom             { TyApp $1 $2 }
  | TyJuxt '(' Type ')'       { TyApp $1 $3 }
  | TyAtom                    { $1 }

TyAtom :: { Type }
  : CONSTR                        { TyCon $ mkId $ constrString $1 }
  | VAR                           { TyVar (mkId $ symString $1) }
  | INT                           { let TokenInt _ x = $1 in TyInt x }
  | TyAtom '+' TyAtom             { TyInfix ("+") $1 $3 }
  | TyAtom '*' TyAtom             { TyInfix ("*") $1 $3 }
  | TyAtom '/' '\\' TyAtom        { TyInfix ("/\\") $1 $4 }
  | TyAtom '\\' '/' TyAtom        { TyInfix ("\\/") $1 $4 }
  | '(' Type '|' Coeffect '|' ')' { Box $4 $2 }
  | '(' TyJuxt ')' { $2 }

Coeffect :: { Coeffect }
  : NatCoeff                    { $1 }
  | '∞'                         { CInfinity (CPoly $ mkInternalId "∞" "infinity") }
  | FLOAT                       { let TokenFloat _ x = $1 in CFloat $ myReadFloat x }
  | CONSTR                      { case (constrString $1) of
                                    "Public" -> Level 0
                                    "Private" -> Level 1
                                    "Inf" -> CInfinity (CPoly $ mkInternalId "∞" "infinity")
                                    x -> error $ "Unknown coeffect constructor `" ++ x ++ "`" }
  | VAR                         { CVar (mkId $ symString $1) }
  | Coeffect '+' Coeffect       { CPlus $1 $3 }
  | Coeffect '*' Coeffect       { CTimes $1 $3 }
  | Coeffect '/' '\\' Coeffect  { CMeet $1 $4 }
  | Coeffect '\\' '/' Coeffect  { CJoin $1 $4 }
  | '(' Coeffect ')'            { $2 }
  | '{' Set '}'                 { CSet $2 }
  | Coeffect ':' CKind          { normalise (CSig $1 $3) }

NatCoeff :: { Coeffect }
  : INT NatModifier           { let TokenInt _ x = $1 in CNat $2 x }

NatModifier :: { NatModifier }
  : {- empty -}               { Ordered }
  | '='                       { Discrete }

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

Expr :: { Expr }
  : let Pat ':' Type '=' Expr in Expr
      { App (getPos $1, getEnd $8) (Val (getSpan $6) (Abs $2 (Just $4) $8)) $6 }

  | let Pat '=' Expr in Expr
      { App (getPos $1, getEnd $6) (Val (getSpan $6) (Abs $2 Nothing $6)) $4 }

  | '\\' '(' Pat ':' Type ')' '->' Expr
      { Val (getPos $1, getEnd $8) (Abs $3 (Just $5) $8) }

  | '\\' Pat '->' Expr
      { Val (getPos $1, getEnd $4) (Abs $2 Nothing $4) }

  | let Pat ':' Type '<-' Expr in Expr
      { LetDiamond (getPos $1, getEnd $8) $2 $4 $6 $8 }

  | case Expr of Cases
      { Case (getPos $1, getEnd . snd . last $ $4) $2 $4 }

  | if Expr then Expr else Expr
      { Case (getPos $1, getEnd $6) $2 [(PConstr (getPosToSpan $3) (mkId "True") [], $4),
                                        (PConstr (getPosToSpan $3) (mkId "False") [], $6)] }

  | Form
    { $1 }

Cases :: { [(Pattern, Expr)] }
 : Case CasesNext             { $1 : $2 }

CasesNext :: { [(Pattern, Expr)] }
  : ';' Cases                 { $2 }
  | {- empty -}               { [] }

Case :: { (Pattern, Expr) }
  : Pat '->' Expr             { ($1, $3) }

Form :: { Expr }
  : Form '+' Form             { Binop (getPosToSpan $2) "+" $1 $3 }
  | Form '-' Form             { Binop (getPosToSpan $2) "-" $1 $3 }
  | Form '*' Form             { Binop (getPosToSpan $2) "*" $1 $3 }
  | Form '<' Form             { Binop (getPosToSpan $2) "<" $1 $3 }
  | Form '>' Form             { Binop (getPosToSpan $2) ">" $1 $3 }
  | Form OP  Form             { Binop (getPosToSpan $2) (symString $2) $1 $3 }
  | Juxt                      { $1 }

Juxt :: { Expr }
  : Juxt '`' Atom '`'         { App (getStart $1, getEnd $3) $3 $1 }
  | Juxt Atom                 { App (getStart $1, getEnd $2) $1 $2 }
  | Atom                      { $1 }

Atom :: { Expr }
  : '(' Expr ')'              { $2 }
  | INT                       { let (TokenInt _ x) = $1
                                in Val (getPosToSpan $1) $ NumInt x }
  | FLOAT                     { let (TokenFloat _ x) = $1
                                in Val (getPosToSpan $1) $ NumFloat $ read x }
  | VAR                       { Val (getPosToSpan $1) $ Var (mkId $ symString $1) }
  | '|' Atom '|'              { Val (getPos $1, getPos $3) $ Promote $2 }
  | CONSTR                    { Val (getPosToSpan $1) $ Constr (mkId $ constrString $1) [] }
  | '(' Expr ',' Expr ')'     { Val (getPos $1, getPos $5) (Pair $2 $4) }
  | CHAR                      { Val (getPosToSpan $1) $
                                  case $1 of (TokenCharLiteral _ c) -> CharLiteral c }
  | STRING                    { Val (getPosToSpan $1) $
                                  case $1 of (TokenStringLiteral _ c) -> StringLiteral c }

{
parseError :: [Token] -> IO a
parseError [] = do
    die "Premature end of file"
parseError t = do
    die $ show l ++ ":" ++ show c ++ ": parse error"
  where (l, c) = getPos (head t)

parseDefs :: (?globals :: Globals) => String -> IO (AST, Int)
parseDefs input = do
    (defs, maxFreshId) <- parse input
    importedDefsAndFreshIds <- forM imports $ \path -> do
      src <- readFile path
      let ?globals = ?globals { sourceFilePath = path }
      parseDefs src
    let (importedDefs, maxFreshIds) = unzip importedDefsAndFreshIds
    -- add defs at the end because definitions
    -- need to precede use sites
    let allDefs = (concat importedDefs) ++ defs
    checkNameClashes allDefs
    let maxFreshId' = if null maxFreshIds then 0 else maximum maxFreshIds
    return (allDefs, maxFreshId `max` maxFreshId')

  where
    parse = fmap (uniqueNames) . defs . scanTokens
    imports = map (("StdLib/" ++ ) . (++ ".gr") . replace '.' '/') . catMaybes
                  . map (stripPrefix "import ") . lines $ input
    replace from to = map (\c -> if c == from then to else c)
    checkNameClashes ds =
        if null clashes
	        then return ()
          else die $ "Error: Name clash: " ++ intercalate ", " (map sourceName clashes)
      where
        clashes = names \\ nub names
        names = (`map` ds) (\d -> case d of (Def _ name _ _ _) -> name
                                            (ADT _ name _ _ _) -> name)
                    

myReadFloat :: String -> Rational
myReadFloat str =
    case readFloat str of
      ((n, []):_) -> n
      _ -> error "Invalid number"

fst3 (a, b, c) = a
snd3 (a, b, c) = b
thd3 (a, b, c) = c
}
