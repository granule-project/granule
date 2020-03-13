{
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Granule.Syntax.Parser
  ( parseDefs
  , parseAndFreshenDefs
  , parseAndDoImportsAndFreshenDefs
  , parseExpr
  , parseTypeScheme
  ) where

import Control.Arrow (first, second, (***), (&&&))
import Control.Monad (forM, when, unless)
import Control.Monad.State (get)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class (lift)
import Data.Char (isSpace)
import Data.Foldable (toList)
import Data.Function (on)
import Data.List (intercalate, nub, stripPrefix)
import Data.Maybe (mapMaybe)
import Data.Set (Set, (\\), fromList, insert, empty, singleton)
import Data.Text (Text)
import qualified Data.Map as M
import Numeric
import System.FilePath ((</>), takeBaseName)
import System.Exit

import Language.Granule.Syntax.Identifiers hiding (mkId)
import Language.Granule.Syntax.Lexer
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.Literal
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Position hiding (startPos)
import qualified Language.Granule.Syntax.Position as P
import Language.Granule.Syntax.Parser.Monad
import Language.Granule.Syntax.Preprocessor.Markdown
import Language.Granule.Syntax.Preprocessor.Latex
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Parser.Tokens
import Language.Granule.Utils hiding (mkSpan)

}

%name topLevel TopLevel
%name program File
%name expr Expr
%name tscheme TypeScheme
%tokentype { Token }
%monad { Parser }
%lexer { lexer } { TokEOF{} }

%token
    data  { TokKeyword KwData $$ }
    where { TokKeyword KwWhere $$ }
    module { TokKeyword KwModule $$ }
    hiding { TokKeyword KwHiding $$ }
    let   { TokKeyword KwLet $$ }
    in    { TokKeyword KwIn  $$  }
    if    { TokKeyword KwIf $$ }
    then  { TokKeyword KwThen $$ }
    else  { TokKeyword KwElse $$ }
    case  { TokKeyword KwCase $$ }
    of    { TokKeyword KwOf $$ }
    import { TokKeyword KwImport $$ }
    -- literal                   { TokLiteral $$ }
    INT   { TokInt $$ }
    FLOAT  { TokFloat $$ }
    VAR    { TokId $$ }
    CONSTR { TokConstr $$ }
    CHAR   { TokCharLiteral $$ }
    STRING { TokStringLiteral $$ }
    forall { TokKeyword KwForall $$ }
    '∞'   { TokSymbol SymInfinity $$ }
    '\\'  { TokSymbol SymLambda $$ }
    '/'  { TokSymbol SymForwardSlash $$ }
    '->'  { TokSymbol SymArrow $$ }
    '<-'  { TokSymbol SymBind $$ }
    '=>'  { TokSymbol SymConstrain $$ }
    ','   { TokSymbol SymComma $$ }
    '×'   { TokSymbol SymCross $$ }
    '='   { TokSymbol SymEqual $$ }
    '=='  { TokSymbol SymEquiv $$ }
    '/='  { TokSymbol SymNeq $$ }
    '+'   { TokSymbol SymPlus $$ }
    '-'   { TokSymbol SymSub $$ }
    '*'   { TokSymbol SymStar $$ }
    '('   { TokSymbol SymOpenParen $$ }
    ')'   { TokSymbol SymCloseParen $$ }
    ':'   { TokSymbol SymSig $$ }
    '['   { TokSymbol SymBoxLeft $$ }
    '{'   { TokSymbol SymOpenBrace $$ }
    '}'   { TokSymbol SymCloseBrace $$ }
    ']'   { TokSymbol SymBoxRight $$ }
    '<'   { TokSymbol SymLangle $$ }
    '>'   { TokSymbol SymRangle $$ }
    '<='  { TokSymbol SymLesserEq $$ }
    '>='  { TokSymbol SymGreaterEq $$ }
    '|'   { TokSymbol SymBar $$ }
    '_'   { TokSymbol SymUnderscore $$ }
    ';'   { TokSymbol SymSemi $$ }
    '.'   { TokSymbol SymDot $$ }
    '`'   { TokSymbol SymBackTick $$ }
    '^'   { TokSymbol SymCaret $$ }
    '..'  { TokSymbol SymDotDot $$ }
    "\\/" { TokSymbol SymJoin $$ }
    "/\\" { TokSymbol SymMeet $$ }
    '∘'   { TokSymbol SymRing $$ }
    '?'   { TokSymbol SymEmptyHole $$ }
    '{!'  { TokSymbol SymHoleStart $$ }
    '!}'  { TokSymbol SymHoleEnd $$ }
    q_id  { TokQId $$ }
    vopen   { TokSymbol SymOpenVirtualBrace $$ }
    vclose  { TokSymbol SymCloseVirtualBrace $$ }
    vsemi   { TokSymbol SymVirtualSemi $$ }

%right '∘'
%right in
%right '->'
%left ':'
%right '×'
%left '..'
%left '+' '-'
%left '*'
%left '^'
%left '|'
%left '.'
%%

File :: { AST () () }
  : TopLevel { $1 }

TopLevel :: { AST () () }
  : module Constr where TopDeclarations
            { $4 { moduleName = Just $ mkId $2 } }

  | module Constr hiding '(' Ids ')' where TopDeclarations
            { let modName = mkId $2
              in $8 { moduleName = Just modName, hiddenNames = $5 modName } }

  | Declarations { $1 }


maybe_vclose :: { () }
maybe_vclose : {- empty -} { () }
             | vclose      { () }


TopDeclarations :: { AST () () }
TopDeclarations
  : {- empty -}   { AST mempty mempty mempty  mempty Nothing }
  | Declarations0 { $1 }


-- Arbitrary declarations
Declarations :: { AST () () }
Declarations
    : vopen Declarations1 close { $2 }

-- Arbitrary declarations (possibly empty)
Declarations0 :: { AST () () }
Declarations0
    : vopen close  { mempty }
    | Declarations { $1 }

Declarations1 :: { AST () () }
Declarations1
    : Declaration semi Declarations1 { $1 <> $3 }
    | Declaration vsemi              { $1 }
    | Declaration                    { $1 }

Declaration :: { AST () () }
  : Def                       { AST [] [$1] mempty mempty Nothing }
  | DataDecl                  { AST [$1] [] mempty mempty Nothing }
  | Import                    { AST [] [] (singleton $1) mempty Nothing }

Ids :: { Id -> M.Map Id Id }
 : Constr          { \modName -> M.insert (mkId $1) modName M.empty }
 | Constr ',' Ids  { \modName -> M.insert (mkId $1) modName ($3 modName) }

-- Defs :: { AST () () }
--   : Def                       { AST [] [$1] mempty mempty Nothing }
--   | DataDecl                  { AST [$1] [] mempty mempty Nothing }
--   | Import                    { AST [] [] (singleton $1) mempty Nothing }
--   | DataDecl NL Defs          { $3 { dataTypes = $1 : dataTypes $3 } }
--   | Def NL Defs               { $3 { definitions = $1 : definitions $3 } }
--   | Import NL Defs            { $3 { imports = insert $1 (imports $3) } }

ModuleName :: { ModuleName }
  : q_id { $1 }

Import :: { Import }
  : import ModuleName { readModuleName $2 }
  -- : import                    { let TokenImport _ ('i':'m':'p':'o':'r':'t':path) = $1
  --                               in dropWhile isSpace path <> ".gr"
  --                             }

Def :: { Def () () }
  : Sig Bindings
  -- : Sig NL Bindings
    {  let name = name2string (fst $1)
       in case $2 of
          (Name _ nameB, _) | not (nameB == name) ->
            error $ "Name for equation `" <> nameB <> "` does not match the signature head `" <> name <> "`"

          (_, bindings) ->
            Def (getSpan' ($1,$2)) (mkId name) False bindings (snd $1)
    }

DataDecl :: { DataDecl }
  : data Constr TyVars where DataConstrs
      { mkDataDecl (getSpan' ($1,$2,$3,$4,$5)) $2 $3 Nothing $5 }
  | data Constr TyVars '=' DataConstrs
      { mkDataDecl (getSpan' ($1,$2,$3,$4,$5)) $2 $3 Nothing $5 }
  | data Constr TyVars KindAnn where DataConstrs
      { mkDataDecl (getSpan' ($1,$2,$3,$4,$5,$6)) $2 $3 (Just $4) $6 }
  | data Constr TyVars KindAnn '=' DataConstrs
      { mkDataDecl (getSpan' ($1,$2,$3,$4,$5,$6)) $2 $3 (Just $4) $6 }

Ident :: { Name }
  : VAR { Name (getRange $ fst $1) (snd $1) }

Constr :: { Name }
  : CONSTR { Name (getRange $ fst $1) (snd $1) }

Sig :: { (Name, TypeScheme) }
  : Ident ':' TypeScheme        { ($1, $3) }

Bindings :: { (Name, EquationList () ()) }
  -- : Binding ';' NL Bindings   { let (v, bind) = $1
  : Binding vsemi Bindings   { let (v, bind) = $1
                                in case $3 of
                                    (v', binds)
                                      | v' == v ->
                                          (v, consEquation bind binds)
                                      | otherwise ->
                                          error $ "Identifier " <> show v' <> " in group of equations does not match " <> show v
                              }
  | Binding                   { case $1 of (v, bind) -> (v, EquationList (equationSpan bind) (mkId v) False [bind]) }

Binding :: { (Name, Equation () ()) }
  : Ident '=' Expr { ($1, Equation (getSpan' ($2,$3)) () False [] $3) }

  | Ident Pats '=' Expr { ($1, Equation (getSpan' ($2,$3,$4)) () False $2 $4) }

-- this was probably a silly idea @buggymcbugfix
  -- | '|' Pats '=' Expr
  --     { (Nothing, Equation (getSpan' ($1,$2,$3,$4)) () False $2 $4) }

DataConstrs :: { [DataConstr] }
  : DataConstr DataConstrNext { $1 : $2 }
  | {- empty -}               { [] }

DataConstr :: { DataConstr }
  : Constr ':' TypeScheme
       { DataConstrIndexed (getSpan' ($1,$2,$3)) (mkId $1) $3 }

  | Constr TyParams
       { DataConstrNonIndexed (getSpan' ($1,$2)) (mkId $1) (fmap getType $2) }

DataConstrNext :: { [DataConstr] }
  : '|' DataConstrs           { $2 }
  | ';' DataConstrs           { $2 }
  | {- empty -}               { [] }

TyVars :: { [(Id', Kind')] }
  : '(' Ident ':' Kind ')' TyVars { (mkId' $2, $4) : $6 }
  | Ident TyVars                  { (mkId' $1, mkKind nullSpanNoFile KType) : $2 }
  | {- empty -}                 { [] }

KindAnn :: { Kind' }
  : ':' Kind                  { $2 }

Pats :: { [Pattern ()] }
  : PAtom                     { [$1] }
  | PAtom Pats                { $1 : $2 }

PAtom :: { Pattern () }
  : Ident
       { PVar (getSpan' $1) () False (mkId $1) }

  | '_'
       { PWild (getSpan' $1) () False }

  | INT
       { let (LitNat _ x) = $1 in PInt (getSpan' $1) () False (fromIntegral x) }

  | FLOAT
       { let (LitFloat _ x) = $1 in PFloat (getSpan' $1) () False x }

  | Constr
       { PConstr (getSpan' $1) () False (mkId $1) [] }

  | '(' NAryConstr ')'        { $2 }

  | '[' PAtom ']'
       { PBox (getSpan' ($1,$2,$3)) () False $2 }

  | '[' NAryConstr ']'
       { PBox (getSpan' ($1,$2,$3)) () False $2 }

  | '(' PMolecule ',' PMolecule ')'
       { PConstr (getSpan' ($1,$2,$3,$4,$5)) () False (mkId ",") [$2, $4] }

PMolecule :: { Pattern () }
  : NAryConstr                { $1 }
  | PAtom                     { $1 }

NAryConstr :: { Pattern () }
  : Constr Pats               { PConstr (getSpan' ($1,$2)) () False (mkId $1) $2 }

ForallSig :: { [(Id', Kind')] }
 : '{' VarSigs '}' { $2 }
 | VarSigs         { $1 }

Forall :: { (([(Id', Kind')]), [Type']) }
 : forall ForallSig '.'                          { ($2, []) }
 | forall ForallSig '.' '{' Constraints '}' '=>' { ($2, $5) }

Constraints :: { [Type'] }
Constraints
 : Constraint ',' Constraints { $1 : $3 }
 | Constraint                 { [$1] }

TypeScheme :: { TypeScheme }
 : Type { Forall nullSpanNoFile [] [] (getType $1) }

 | Forall Type
       { mkForall (getSpan' ($1,$2)) (fst $1) (snd $1) $2 }

VarSigs :: { [(Id', Kind')] }
  : VarSig ',' VarSigs        { $1 <> $3 }
  | VarSig                    { $1 }

VarSig :: { [(Id', Kind')] }
  : Vars1 ':' Kind            { fmap (\id -> (mkId' id, $3)) $1 }
  | Vars1                     { flip concatMap $1 (\id ->
                                  let k = mkId (prependToName "_k" id)
                                  in [(mkId' id, mkKind (getSpan' id) (KVar k))]) }

-- A non-empty list of variables
Vars1 :: { [Name] }
  : Ident                       { [$1] }
  | Ident Vars1                 { $1 : $2 }

Kind :: { Kind' }
  : Kind '->' Kind            { mkKind (getSpan' ($1,$2,$3)) $ KFun (getKind $1) (getKind $3) }
  | Ident                       { mkKind (getSpan' $1) $ KVar (mkId $1) }
  | Constr                    { mkKind (getSpan' $1) $
                                 case name2string $1 of
                                  "Type"      -> KType
                                  "Coeffect"  -> KCoeffect
                                  "Predicate" -> KPredicate
                                  s          -> kConstr $ mkId s }
  | '(' TyJuxt TyAtom ')'     { mkKind (getSpan' ($1,$2,$3,$4)) $ KPromote (TyApp (getType $2) (getType $3)) }
  | TyJuxt TyAtom             { mkKind (getSpan' ($1,$2)) $ KPromote (TyApp (getType $1) (getType $2)) }


Type :: { Type' }
  : '(' Ident ':' Type ')' '->' Type { mkType (getSpan' ($1,$2,$3,$4,$5,$6,$7)) $ FunTy (Just . mkId $ $2) (getType $4) (getType $7) }
  | TyJuxt                         { mkType (getSpan' $1) (getType $1) }
  | Type '->' Type                 { mkType (getSpan' ($1,$2,$3)) $ FunTy Nothing (getType $1) (getType $3) }
  | Type '×' Type                  { mkType (getSpan' ($1,$2,$3)) $ TyApp (TyApp (TyCon $ mkId ",") (getType $1)) (getType $3) }
  | TyAtom '[' Coeffect ']'        { mkType (getSpan' ($1,$2,$3,$4)) $ Box (getCoeff $3) (getType $1) }
  | TyAtom '[' ']'                 { mkType (getSpan' ($1,$2,$3)) $ Box (CInterval (CZero extendedNat) infinity) (getType $1) }
  | TyAtom '<' Effect '>'          { mkType (getSpan' ($1,$2,$3,$4)) $ Diamond (getType $3) (getType $1) }

-- TyApp :: { Type }
--  : TyJuxt TyAtom              { TyApp $1 $2 }
--  | TyAtom                     { $1 }

TyJuxt :: { Type' }
  : TyJuxt '`' TyAtom '`'     { mkType (getSpan' ($1,$2,$3,$4)) $ TyApp (getType $3) (getType $1) }
  | TyJuxt TyAtom             { mkType (getSpan' ($1, $2)) $ TyApp (getType $1) (getType $2) }
  | TyAtom                    { $1 }
  | TyAtom '+' TyAtom         { mkType (getSpan' ($1,$2,$3)) $ TyInfix TyOpPlus (getType $1) (getType $3) }
  | TyAtom '-' TyAtom         { mkType (getSpan' ($1,$2,$3)) $ TyInfix TyOpMinus (getType $1) (getType $3) }
  | TyAtom '*' TyAtom         { mkType (getSpan' ($1,$2,$3)) $ TyInfix TyOpTimes (getType $1) (getType $3) }
  | TyAtom '^' TyAtom         { mkType (getSpan' ($1,$2,$3)) $ TyInfix TyOpExpon (getType $1) (getType $3) }
  | TyAtom "/\\" TyAtom       { mkType (getSpan' ($1,$2,$3)) $ TyInfix TyOpMeet (getType $1) (getType $3) }
  | TyAtom "\\/" TyAtom       { mkType (getSpan' ($1,$2,$3)) $ TyInfix TyOpJoin (getType $1) (getType $3) }

Constraint :: { Type' }
  : TyAtom '>' TyAtom         { mkType (getSpan' ($1,$2,$3)) $ TyInfix TyOpGreater (getType $1) (getType $3) }
  | TyAtom '<' TyAtom         { mkType (getSpan' ($1,$2,$3)) $ TyInfix TyOpLesser (getType $1) (getType $3) }
  | TyAtom '<=' TyAtom        { mkType (getSpan' ($1,$2,$3)) $ TyInfix TyOpLesserEq (getType $1) (getType $3) }
  | TyAtom '>=' TyAtom        { mkType (getSpan' ($1,$2,$3)) $ TyInfix TyOpGreaterEq (getType $1) (getType $3) }
  | TyAtom '==' TyAtom        { mkType (getSpan' ($1,$2,$3)) $ TyInfix TyOpEq (getType $1) (getType $3) }
  | TyAtom '/=' TyAtom        { mkType (getSpan' ($1,$2,$3)) $ TyInfix TyOpNotEq (getType $1) (getType $3) }

TyAtom :: { Type' }
  : Constr                    { mkType (getSpan' $1) $ TyCon $ mkId $1 }
  | Ident                     { mkType (getSpan' $1) $ TyVar (mkId $1) }
  | INT                       { mkType (getSpan' $1) $ let (LitNat _ x) = $1 in TyInt (fromIntegral x) }
  | '(' Type ')'              { $2 }
  | '(' Type ',' Type ')'     { mkType (getSpan' ($1,$2,$3,$4,$5)) $ TyApp (TyApp (TyCon $ mkId ",") (getType $2)) (getType $4) }

TyParams :: { [Type'] }
  : TyAtom TyParams           { $1 : $2 } -- use right recursion for simplicity -- VBL
  |                           { [] }

Coeffect :: { Coeffect' }
  : INT                         { mkCoeff (getSpan' $1) $ let (LitNat _ x) = $1 in CNat (fromIntegral x) }
  | '∞'                         { mkCoeff (getSpan' $1) $ infinity }
  | FLOAT                       { mkCoeff (getSpan' $1) $ let (LitFloat _ x) = $1 in CFloat $ toRational x }
  | Constr                      { mkCoeff (getSpan' $1) $
                                   case (name2string $1) of
                                    "Public" -> Level publicRepresentation
                                    "Private" -> Level privateRepresentation
                                    "Unused" -> Level unusedRepresentation
                                    "Inf" -> infinity
                                    x -> error $ "Unknown coeffect constructor `" <> x <> "`" }
  | Ident                         { mkCoeff (getSpan' $1) $ CVar (mkId $1) }
  | Coeffect '..' Coeffect      { mkCoeff (getSpan' ($1,$2,$3)) $ CInterval (getCoeff $1) (getCoeff $3) }
  | Coeffect '+' Coeffect       { mkCoeff (getSpan' ($1,$2,$3)) $ CPlus (getCoeff $1) (getCoeff $3) }
  | Coeffect '*' Coeffect       { mkCoeff (getSpan' ($1,$2,$3)) $ CTimes (getCoeff $1) (getCoeff $3) }
  | Coeffect '-' Coeffect       { mkCoeff (getSpan' ($1,$2,$3)) $ CMinus (getCoeff $1) (getCoeff $3) }
  | Coeffect '^' Coeffect       { mkCoeff (getSpan' ($1,$2,$3)) $ CExpon (getCoeff $1) (getCoeff $3) }
  | Coeffect "/\\" Coeffect     { mkCoeff (getSpan' ($1,$2,$3)) $ CMeet (getCoeff $1) (getCoeff $3) }
  | Coeffect "\\/" Coeffect     { mkCoeff (getSpan' ($1,$2,$3)) $ CJoin (getCoeff $1) (getCoeff $3) }
  | '(' Coeffect ')'            { $2 }
  | '{' Set '}'                 { mkCoeff (getSpan' ($1,$2,$3)) $ CSet (fmap (name2string *** getType) $2) }
  | Coeffect ':' Type           { mkCoeff (getSpan' ($1,$2,$3)) $ normalise (CSig (getCoeff $1) (getType $3)) }
  | '(' Coeffect ',' Coeffect ')' { mkCoeff (getSpan' ($1,$2,$3,$4)) $ CProduct (getCoeff $2) (getCoeff $4) }

Set :: { [(Name, Type')] }
  : Ident ':' Type ',' Set      { ($1, $3) : $5 }
  | Ident ':' Type              { [($1, $3)] }

Effect :: { Type' }
  : '{' EffSet '}'            { mkType (getSpan' ($1,$2,$3)) $ TySet (fmap getType $2) }
  | {- EMPTY -}               { mkType nullSpanNoFile $ TyCon $ mkId "Pure" }
  | TyJuxt                    { $1 }

EffSet :: { [Type'] }
  : Eff ',' EffSet         { $1 : $3 }
  | Eff                    { [$1] }

Eff :: { Type' }
  : Constr                  { mkType (getSpan' $1) $ TyCon $ mkId $1 }

Expr :: { Expr () () }
  : let LetBind MultiLet
      { let (pat, mt, expr) = $2
      	in App (getSpan' ($1,$2,$3)) () False
             (Val (getSpan' $3) () False (Abs () pat (fmap getType mt) $3)) expr
      }

  | '\\' '(' PAtom ':' Type ')' '->' Expr
    { Val (getSpan' ($1,$2,$3,$4,$5,$6,$7,$8)) () False (Abs () $3 (Just (getType $5)) $8) }

  | '\\' PAtom '->' Expr
    { Val (getSpan' ($1,$2,$3,$4)) () False (Abs () $2 Nothing $4) }

  | let LetBindEff MultiLetEff
    { let (pat, mt, expr) = $2 in LetDiamond (getSpan' ($1,$2,$3)) () False pat (fmap getType mt) expr $3 }

  | case Expr of Cases
    { Case (getSpan' ($1,$2,$3,$4)) () False $2 $4 }

  | if Expr then Expr else Expr
    { Case (getSpan' ($1,$2,$3,$4,$5,$6)) () False $2
       [(PConstr (getSpan' $4) () False (mkId "True") [], $4),
        (PConstr (getSpan' $6) () False (mkId "False") [], $6)] }

  | Form
    { $1 }

LetBind :: { (Pattern (), Maybe Type', Expr () ()) }
  : PAtom ':' Type '=' Expr
      { ($1, Just $3, $5) }
  | PAtom '=' Expr
      { ($1, Nothing, $3) }
  | NAryConstr ':' Type '=' Expr
      { ($1, Just $3, $5) }
  | NAryConstr '=' Expr
      { ($1, Nothing, $3) }

MultiLet :: { Expr () () }
MultiLet
  : ';' LetBind MultiLet
    { let (pat, mt, expr) = $2
      in App (getSpan' ($1,$2,$3)) () False
     	     (Val (getSpan' $3) () False (Abs () pat (fmap getType mt) $3)) expr }
  | in Expr
    { $2 }

LetBindEff :: { (Pattern (), Maybe Type', Expr () ()) }
  : PAtom '<-' Expr            { ($1, Nothing, $3) }
  | PAtom ':' Type '<-' Expr   { ($1, Just $3, $5) }

MultiLetEff :: { Expr () () }
MultiLetEff
  : ';' LetBindEff MultiLetEff
      { let (pat, mt, expr) = $2
	in LetDiamond (getSpan' ($1,$2,$3)) () False pat (fmap getType mt) expr $3
      }
  | in Expr                   { $2 }

Cases :: { [(Pattern (), Expr () () )] }
 : Case CasesNext             { $1 : $2 }

CasesNext :: { [(Pattern (), Expr () ())] }
  : ';' Cases                 { $2 }
  | {- empty -}               { [] }

Case :: { (Pattern (), Expr () ()) }
  : PAtom '->' Expr           { ($1, $3) }
  | NAryConstr '->' Expr      { ($1, $3) }

Form :: { Expr () () }
  : Form '+' Form  { Binop (getSpan' ($1,$2,$3)) () False OpPlus $1 $3 }
  | Form '-' Form  { Binop (getSpan' ($1,$2,$3)) () False OpMinus $1 $3 }
  | Form '*' Form  { Binop (getSpan' ($1,$2,$3)) () False OpTimes $1 $3 }
  | Form '<' Form  { Binop (getSpan' ($1,$2,$3)) () False OpLesser $1 $3 }
  | Form '>' Form  { Binop (getSpan' ($1,$2,$3)) () False OpGreater $1 $3 }
  | Form '<=' Form { Binop (getSpan' ($1,$2,$3)) () False OpLesserEq $1 $3 }
  | Form '>=' Form { Binop (getSpan' ($1,$2,$3)) () False OpGreaterEq $1 $3 }
  | Form '==' Form { Binop (getSpan' ($1,$2,$3)) () False OpEq $1 $3 }
  | Form '/=' Form { Binop (getSpan' ($1,$2,$3)) () False OpNotEq $1 $3 }
  | Form '∘'  Form { App (getSpan' ($1,$2,$3)) () False (App (getSpan' ($1,$2,$3)) () False (Val (getSpan' ($1,$2,$3)) () False (Var () (mkId "compose"))) $1) $3 }
  | Juxt           { $1 }

Juxt :: { Expr () () }
  : Juxt '`' Atom '`'         { App (getSpan' ($1,$2,$3)) () False $3 $1 }
  | Juxt Atom                 { App (getSpan' ($1,$2)) () False $1 $2 }
  | Atom                      { $1 }

Hole :: { Expr () () }
  : '{!' Vars1 '!}'           { Hole (getSpan' ($1,$2,$3)) () False (map mkId $2) }
  | '{!' '!}'                 { Hole (getSpan' ($1,$2)) () False [] }
  | '?'                       { Hole (getSpan' $1) () False [] }

Atom :: { Expr () () }
  : '(' Expr ')'              { $2 }
  | INT                       { let (LitNat _ x) = $1
                                in Val (getSpan' $1) () False $ NumInt (fromIntegral x) }
  -- | '<' Expr '>'              { App (getSpan' ($1,$2,$3)) () False (Val (getSpan' ($1,$2,$3)) () (Var () (mkId "pure"))) $2 }
  | FLOAT                     { let (LitFloat _ x) = $1
                                in Val (getSpan' $1) () False $ NumFloat x }

  | Ident                       { Val (getSpan' $1) () False $ Var () (mkId $1) }

  | '[' Expr ']'              { Val (getSpan' ($1,$2,$3)) () False $ Promote () $2 }
  | Constr                    { Val (getSpan' $1) () False $ Constr () (mkId $1) [] }
  | '(' Expr ',' Expr ')'
    { App (getSpan' ($1,$2,$3,$4,$5)) () False
            (App (getSpan' ($1,$2,$3)) () False
                   (Val (getSpan' $3) () False (Constr () (mkId ",") [])) $2) $4 }
  | CHAR                      { Val (getSpan' $1) () False (CharLiteral $ getLitChar $1) }
  | STRING                    { Val (getSpan' $1) () False $ (StringLiteral $ getLitString $1) }
  | Hole                      { $1 }


{--------------------------------------------------------------------------
    Meta rules (from Agda)
 --------------------------------------------------------------------------}

-- The first token in a file decides the indentation of the top-level layout
-- block. Or not. It will if we allow the top-level module to be omitted.
-- topen :      {- empty -}     {% pushCurrentContext }


{-  A layout block might have to be closed by a parse error. Example:
        let x = e in e'
    Here the 'let' starts a layout block which should end before the 'in'.  The
    problem is that the lexer doesn't know this, so there is no virtual close
    brace. However when the parser sees the 'in' there will be a parse error.
    This is our cue to close the layout block.
-}
close :: { () }
close : vclose  { () }
      | error   {% popContext }


-- You can use concrete semi colons in a layout block started with a virtual
-- brace, so we don't have to distinguish between the two semi colons. You can't
-- use a virtual semi colon in a block started by a concrete brace, but this is
-- simply because the lexer will not generate virtual semis in this case.
semi :: { Interval }
semi : ';'    { $1 }
     | vsemi  { $1 }


-- Enter the 'imp_dir' lex state, where we can parse the keyword 'to'.
beginImpDir :: { () }
beginImpDir : {- empty -}   {% pushLexState imp_dir }

{

mkSpan :: (Pos, Pos) -> Parser Span
mkSpan (start, end) = do
  filename <- maybe "" id . parseSrcFile <$> get
  return $ Span start end filename

-- TODO: once we support parsing modules, remove the 'layout' fragment here, as
-- this should be handled by the fact that 'where' is a layout keyword (2020-03-10)
parseProgram :: FilePath -> String -> ParseResult (AST () ())
parseProgram file = parseFromSrc defaultParseFlags [layout, normal] program (Just file)

parseDefs = parseProgram

parseExpr :: FilePath -> String -> ParseResult (Expr () ())
parseExpr file = parseFromSrc defaultParseFlags [layout, normal] expr (Just file)

parseTypeScheme :: FilePath -> String -> ParseResult TypeScheme
parseTypeScheme file = parseFromSrc defaultParseFlags [layout, normal] tscheme (Just file)

parseAndDoImportsAndFreshenDefs :: (?globals :: Globals) => String -> IO (AST () ())
parseAndDoImportsAndFreshenDefs input = do
    ast <- parseDefsAndDoImports input
    return $ freshenAST ast

parseAndFreshenDefs :: (?globals :: Globals) => String -> IO (AST () ())
parseAndFreshenDefs input = do
  let res = parseProgram sourceFilePath input
  case res of
    ParseOk _ ast -> pure $ freshenAST ast
    ParseFailed err -> failWithErr err

parseDefsAndDoImports :: (?globals :: Globals) => String -> IO (AST () ())
parseDefsAndDoImports input = do
    let res = parseProgram sourceFilePath input
    ast <- case res of
             ParseOk _ ast -> pure ast
             ParseFailed err -> failWithErr err
    case moduleName ast of
      Nothing -> doImportsRecursively (imports ast) (ast { imports = empty })
      Just (Id name _) ->
        if name == takeBaseName sourceFilePath
          then doImportsRecursively (imports ast) (ast { imports = empty })
          else do
            failWithMsg $ "Module name `" <> name <> "` does not match filename `" <> takeBaseName sourceFilePath <> "`"

  where
    -- Get all (transitive) dependencies. TODO: blows up when the file imports itself
    doImportsRecursively :: Set Import -> AST () () -> IO (AST () ())
    doImportsRecursively todo ast@(AST dds defs done hidden name) = do
      case toList (todo \\ done) of
        [] -> return ast
        (i:todo) ->
          let path = includePath </> i in
          let ?globals = ?globals { globalsSourceFilePath = Just path } in do
            src <- readFile path
            let res = parseProgram sourceFilePath input
            ast <- case res of
                     ParseOk _ ast -> pure ast
                     ParseFailed err -> failWithErr err
            let (AST dds' defs' imports' hidden' _) = ast
            doImportsRecursively
              (fromList todo <> imports')
              (AST (dds' <> dds) (defs' <> defs) (insert i done) (hidden `M.union` hidden') name)

failWithMsg :: String -> IO a
failWithMsg msg = putStrLn msg >> exitFailure

lastSpan [] = fst $ nullSpanLocs
lastSpan xs = getEnd . snd . last $ xs

lastSpan' [] = fst $ nullSpanLocs
lastSpan' xs = endPos $ getSpan (last xs)

fst3 (a, b, c) = a
snd3 (a, b, c) = b
thd3 (a, b, c) = c

type ModuleName = [(Interval, String)]
readModuleName :: ModuleName -> String
readModuleName [] = []
readModuleName mn = intercalate "/" (fmap snd mn) <> ".gr"

textToString :: Text -> String
textToString = show

rangeToSpan :: Range -> Span
rangeToSpan NoRange = nullSpanNoFile
rangeToSpan r =
  let name = maybe "" id (rangeFile r)
      toPos = (fromIntegral . posLine) &&& (fromIntegral . posCol)
      sp = maybe (0, 0) toPos (rStart' r)
      ep = maybe sp toPos (rEnd' r)
  in Span { filename = name, startPos = sp, endPos = ep }

getSpan' :: (HasRange a) => a -> Span
getSpan' = rangeToSpan . getRange

instance HasRange Span where
  getRange s =
    let fname = Just $ filename s
        both f (x, y) = (f x, f y)
        (startLine, startCol) = both fromIntegral (startPos s)
        (endLine, endCol) = both fromIntegral (endPos s)
        posStart = (P.startPos' ()) { posLine = startLine, posCol = startCol }
        posEnd = (P.startPos' ()) { posLine = endLine, posCol = endCol }
    in posToRange' fname posStart posEnd

spanToRange :: Span -> Range
spanToRange = getRange

instance HasRange (EquationList v a) where
  getRange = spanToRange . equationsSpan

getLitChar :: Literal -> Char
getLitChar (LitChar _ c) = c
getLitChar _ = error "getLitChar called with non-char"

getLitString :: Literal -> Text
getLitString (LitString _ s) = read s
getLitString _ = error "getLitString called with non-string"

mkDataDecl :: Span -> Name -> [(Id', Kind')] -> Maybe Kind' -> [DataConstr] -> DataDecl
mkDataDecl s n ctx k = DataDecl s (mkId n) (fmap (getId *** getKind) ctx) (fmap getKind k)


mkForall :: Span -> [(Id', Kind')] -> [Type'] -> Type' -> TypeScheme
mkForall s iks ts t = Forall s (fmap (mkId *** getKind) iks) (fmap getType ts) (getType t)


failWithErr :: ParseError -> _
failWithErr = failWithMsg . showErr


showErr :: ParseError -> String
showErr = show


-----------------------------
----- Wrapper datatypes -----
-----------------------------


{-

  These wrappers exist to add spans to some of Granule's datatypes, which currently
  dont' have them (e.g., Coeffect and Type).

-}


data Kind' = Kind' { kindRange :: Range, getKind :: Kind }


instance HasRange Kind' where
  getRange = kindRange


mkKind :: Span -> Kind -> Kind'
mkKind s k = Kind' (spanToRange s) k


data Type' = Type' { typeRange :: Range, getType :: Type }


instance HasRange Type' where
  getRange = typeRange


mkType :: Span -> Type -> Type'
mkType s t = Type' { typeRange = spanToRange s, getType = t }


data Name = Name { nameRange :: Range, name2string :: String }
  deriving (Show)


instance HasRange Name where
  getRange = nameRange


instance Eq Name where
  -- don't care about ranges when checking for equality
  (==) = (==) `on` name2string


prependToName :: String -> Name -> Name
prependToName s n = n { name2string = s <> name2string n }


data Id' = Id' { idRange :: Range, getId :: Id }


instance HasRange Id' where
  getRange = idRange


class ToId a where
  mkId :: a -> Id


instance ToId String where
  mkId x = Id x x


instance ToId Name where
  mkId = mkId . name2string


instance ToId Id' where
  mkId = getId


class ToId' a where
  mkId' :: a -> Id'


instance ToId' Name where
  mkId' x = Id' { idRange = getRange x, getId = mkId x }


instance HasRange (Expr v a) where
  getRange = spanToRange . getSpan


instance HasRange (Pattern a) where
  getRange = spanToRange . getSpan


instance HasRange TypeScheme where
  getRange = spanToRange . getSpan


instance HasRange DataConstr where
  getRange = spanToRange . getSpan


-- instance {-# OVERLAPPABLE #-} (FirstParameter a Span) => HasRange a where
--   getRange = spanToRange . getSpan


data Coeffect' = Coeffect' { coeffRange :: Range, getCoeff :: Coeffect }


instance HasRange Coeffect' where
  getRange = coeffRange


mkCoeff :: Span -> Coeffect -> Coeffect'
mkCoeff s c = Coeffect' { coeffRange = spanToRange s, getCoeff = c }


---------------------------
----- Stuff for Happy -----
---------------------------


-- | Required by Happy.
happyError :: Parser a
happyError = parseError "Parse error"


}
