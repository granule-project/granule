{
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Granule.Syntax.Parser where

import Control.Monad (forM)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class (lift)
import Data.List ((\\), intercalate, nub, stripPrefix)
import Data.Maybe (mapMaybe)
import Numeric
import System.Exit (die)
import System.FilePath ((</>))

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Lexer
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Preprocessor.Markdown
import Language.Granule.Syntax.Preprocessor.Latex
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Utils hiding (mkSpan)

}

%name defs Defs
%name expr Expr
%name tscheme TypeScheme
%tokentype { Token }
%error { parseError }
%monad { ReaderT String (Either String) }

%token
    nl    { TokenNL _ }
    data  { TokenData _ }
    interface { TokenIFace _ }
    instance  { TokenInst _ }
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
    '=>'  { TokenConstrain _ }
    ','   { TokenComma _ }
    '×'   { TokenCross _ }
    '='   { TokenEq _ }
    '/='  { TokenNeq _ }
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
    OP    { TokenOp _ _ }
    '<='   { TokenOp _ "≤" }
    '>='   { TokenOp _ "≥" }
    '|'   { TokenPipe _ }
    '_'   { TokenUnderscore _ }
    ';'   { TokenSemicolon _ }
    '.'   { TokenPeriod _ }
    '`'   { TokenBackTick _ }
    '^'   { TokenCaret _ }
    ".."  { TokenDotDot _ }
    "∨"   { TokenJoin _ }
    "∧"   { TokenMeet _ }

%right in
%right '->'
%left ':'
%right '×'
%left ".."
%left '+' '-'
%left '*'
%left '^'
%left '|'
%left '.'
%%

Defs :: { AST () () }
  : Def                       { AST [] [$1] [] [] }

  | DataDecl                  { AST [$1] [] [] [] }

  | DataDecl NL Defs          { let (AST dds defs ifaces insts) = $3
                                 in AST ($1 : dds) defs ifaces insts }

  | IFaceDecl                 { AST [] [] [$1] [] }

  | IFaceDecl NL Defs         { let (AST dds defs ifaces insts) = $3
                                 in AST dds defs ($1 : ifaces) insts }

  | InstDecl                  { AST [] [] [] [$1] }

  | InstDecl NL Defs          { let (AST dds defs ifaces insts) = $3
                                 in AST dds defs ifaces ($1 : insts) }

  | Def NL Defs               { let (AST dds defs ifaces insts) = $3
                                 in AST dds ($1 : defs) ifaces insts }

NL :: { () }
  : nl NL                    { }
  | nl                       { }

Def :: { Def () () }
  : Sig NL Bindings
    {% let name = fst3 $1
       in case $3 of
          (Just nameB, _) | not (nameB == name) ->
            error $ "Name for equation `" <> nameB <> "` does not match the signature head `" <> name <> "`"
          (_, bindings) -> do
            span <- mkSpan (thd3 $1, endPos $ getSpan $ last bindings)
            return $ Def span (mkId name) bindings (snd3 $1)
    }

DataDecl :: { DataDecl }
  : data CONSTR TyVars KindAnn where DataConstrs
      {% do
          span <- mkSpan (getPos $1, lastSpan' $6)
          return $ DataDecl span (mkId $ constrString $2) $3 $4 $6 }
  | data CONSTR TyVars KindAnn '=' DataConstrs
      {% do
          span <- mkSpan (getPos $1, lastSpan' $6)
          return $ DataDecl span (mkId $ constrString $2) $3 $4 $6 }

IFaceName :: { Id }
  : CONSTR { mkId $ constrString $1 }

IFaceConstrained :: { [TConstraint] }
  : '{' Constraints '}' '=>' { $2 }

IFaceVars :: { (Span, [(Id, Maybe Kind)]) }
  : IFaceVar IFaceVars { % mkSpan (getStart $1, getEnd $2) >>= \sp -> pure (sp, snd $1 : snd $2) }
  | IFaceVar { (fst $1, [snd $1]) }

IFaceVar :: { (Span, (Id, Maybe Kind)) }
  : VAR            { % mkSpan (getPosToSpan $1)      >>= \sp -> return $ (sp, (mkId $ symString $1, Nothing)) }
  | '(' VarSig ')' { % mkSpan (getPos $1, getPos $3) >>= \sp -> return $ (sp, (fst $2, Just (snd $2))) }

IFaceSigs :: { [IFaceTy] }
  : Sig ';' IFaceSigs
    { % mkSpan (thd3 $1, getEnd $ snd3 $1) >>= \sp -> return $ IFaceTy sp (mkId $ fst3 $1) (snd3 $1) : $3 }
  | Sig
    { % mkSpan (thd3 $1, getEnd $ snd3 $1) >>= \sp -> return $ [IFaceTy sp (mkId $ fst3 $1) (snd3 $1)] }

IFaceDecl :: { Interface }
  : interface IFaceName IFaceVars where IFaceSigs
  { % mkSpan (getPos $1, lastSpan' $5) >>= \sp -> return $ Interface sp $2 [] (snd $3) $5 }
  | interface IFaceConstrained IFaceName IFaceVars where IFaceSigs
  { % mkSpan (getPos $1, lastSpan' $6) >>= \sp -> return $ Interface sp $3 $2 (snd $4) $6 }
  | interface IFaceName IFaceVars
  { % mkSpan (getPos $1, endPos (fst $3)) >>= \sp -> return $ Interface sp $2 [] (snd $3) [] }
  | interface IFaceConstrained IFaceName IFaceVars
  { % mkSpan (getPos $1, endPos (fst $4)) >>= \sp -> return $ Interface sp $3 $2 (snd $4) [] }

InstBinds :: { [IDef () ()] }
  : NamedBinding ';' InstBindsRest
    { % mkSpan (snd $ fst $1, getEnd $ snd $1) >>= \sp -> return $ IDef sp (fmap mkId $ fst $ fst $1) (snd $1) : $3 }
  | NamedBinding
    { % mkSpan (snd $ fst $1, getEnd $ snd $1) >>= \sp -> return [IDef sp (fmap mkId $ fst $ fst $1) (snd $1)] }

InstBindsRest :: { [IDef () ()] }
  : Binding ';' InstBindsRest
    { % mkSpan (snd $ fst $1, getEnd $ snd $1) >>= \sp -> return $ IDef sp (fmap mkId $ fst $ fst $1) (snd $1) : $3 }
  | Binding
    { % mkSpan (snd $ fst $1, getEnd $ snd $1) >>= \sp -> return [IDef sp (fmap mkId $ fst $ fst $1) (snd $1)] }

InstTys :: { (Span, [Type]) }
  : InstTy InstTys { % mkSpan (getStart $1, getEnd $2) >>= \sp -> pure (sp, snd $1 : snd $2) }
  | InstTy { (fst $1, [snd $1]) }

InstTy :: { (Span, Type) }
  : TyAtomWithSpan { (snd $1, fst $1) }

InstForm :: { IFaceDat }
  : InstTys { IFaceDat (fst $1) (snd $1) }

InstDecl :: { Instance () ()  }
  : instance IFaceName InstForm where InstBinds
    { % mkSpan (getPos $1, getEnd . last $ $5) >>= \sp -> return $ Instance sp $2 [] $3 $5 }
  | instance IFaceConstrained IFaceName InstForm where InstBinds
    { % mkSpan (getPos $1, getEnd . last $ $6) >>= \sp -> return $ Instance sp $3 $2 $4 $6 }
  | instance IFaceName InstForm
    { % mkSpan (getPos $1, getEnd $3) >>= \sp -> return $ Instance sp $2 [] $3 [] }
  | instance IFaceConstrained IFaceName InstForm
    { % mkSpan (getPos $1, getEnd $4) >>= \sp -> return $ Instance sp $3 $2 $4 [] }

Sig :: { (String, TypeScheme, Pos) }
  : VAR ':' TypeScheme        { (symString $1, $3, getPos $1) }

Bindings :: { (Maybe String, [Equation () ()]) }
  : Binding ';' NL Bindings   { let ((v, _), bind) = $1
                                in case $4 of
                                    (v', binds)
                                      | v' == v || v' == Nothing ->
                                          (v, (bind : binds))
                                      | otherwise ->
                                          error $ "Identifier " <> show v' <> " in group of equations does not match " <> show v
                              }
  | Binding                   { case $1 of ((v, _), bind) -> (v, [bind]) }

Binding :: { ((Maybe String, Pos), Equation () ()) }
  : NamedBinding { $1 }
  | GuardBinding { $1 }

NamedBinding :: { ((Maybe String, Pos), Equation () ()) }
  : VAR '=' Expr
      {% do
          span <- mkSpan (getPos $1, getEnd $3)
          return ((Just $ symString $1, getPos $1), Equation span () [] $3) }

  | VAR Pats '=' Expr
      {% do
          span <- mkSpan (getPos $1, getEnd $4)
          return ((Just $ symString $1, getPos $1), Equation span () $2 $4) }

GuardBinding :: { ((Maybe String, Pos), Equation () ()) }
  : '|' Pats '=' Expr
      {% do
          span <- mkSpan (getPos $1, getEnd $4)
          return ((Nothing, getPos $1), Equation span () $2 $4) }

DataConstrs :: { [DataConstr] }
  : DataConstr DataConstrNext { $1 : $2 }
  | {- empty -}               { [] }

DataConstr :: { DataConstr }
  : CONSTR ':' TypeScheme
       {% do span <- mkSpan (getPos $1, getEnd $3)
             return $ DataConstrIndexed span (mkId $ constrString $1) $3 }

  | CONSTR TyParams
       {% do span <- mkSpan (getPosToSpan $1)
             return $ DataConstrNonIndexed span (mkId $ constrString $1) $2 }

DataConstrNext :: { [DataConstr] }
  : '|' DataConstrs           { $2 }
  | ';' DataConstrs           { $2 }
  | {- empty -}               { [] }

TyVars :: { [(Id, Kind)] }
  : '(' VAR ':' Kind ')' TyVars { (mkId $ symString $2, $4) : $6 }
  | VAR TyVars                  { (mkId $ symString $1, KType) : $2 }
  | {- empty -}                 { [] }

KindAnn :: { Maybe Kind }
  : ':' Kind                  { Just $2 }
  | {- empty -}               { Nothing }

Pats :: { [Pattern ()] }
  : PAtom                     { [$1] }
  | PAtom Pats                { $1 : $2 }

PAtom :: { Pattern () }
  : VAR
       {% (mkSpan $ getPosToSpan $1) >>= \sp -> return $ PVar sp () (mkId $ symString $1) }

  | '_'
       {% (mkSpan $ getPosToSpan $1) >>= \sp -> return $ PWild sp () }

  | INT
       {% (mkSpan $ getPosToSpan $1) >>= \sp -> return $ let TokenInt _ x = $1 in PInt sp () x }

  | FLOAT
       {% (mkSpan $ getPosToSpan $1) >>= \sp -> return $ let TokenFloat _ x = $1 in PFloat sp () $ read x }

  | CONSTR
       {% (mkSpan $ getPosToSpan $1) >>= \sp -> return $ let TokenConstr _ x = $1 in PConstr sp () (mkId x) [] }

  | '(' NAryConstr ')'        { $2 }

  | '[' PAtom ']'
       {% (mkSpan (getPos $1, getPos $3)) >>= \sp -> return $ PBox sp () $2 }

  | '[' NAryConstr ']'
       {% (mkSpan (getPos $1, getPos $3)) >>= \sp -> return $ PBox sp () $2 }

  | '(' PAtom ',' PAtom ')'
       {% (mkSpan (getPos $1, getPos $5)) >>= \sp -> return $ PConstr sp () (mkId ",") [$2, $4] }

NAryConstr :: { Pattern () }
  : CONSTR Pats               {% let TokenConstr _ x = $1
                                in (mkSpan (getPos $1, getEnd $ last $2)) >>=
                                       \sp -> return $ PConstr sp  () (mkId x) $2 }

ForallSig :: { [(Id, Kind)] }
 : '{' VarSigs '}' { $2 }
 | VarSigs         { $1 }

Forall :: { (((Pos, Pos), [(Id, Kind)]), [Type]) }
 : forall ForallSig '.'                       { (((getPos $1, getPos $3), $2), []) }
 | forall ForallSig '.' '{' Constraints '}' '=>' { (((getPos $1, getPos $7), $2), $5) }

Constraints :: { [Type] }
Constraints
 : Constraint ',' Constraints { $1 : $3 }
 | Constraint                 { [$1] }

TypeScheme :: { TypeScheme }
 : Type
       {% return $ Forall nullSpanNoFile [] [] $1 }

 | Forall Type
       {% (mkSpan (fst $ fst $1)) >>= \sp -> return $ Forall sp (snd $ fst $1) (snd $1) $2 }

VarSigs :: { [(Id, Kind)] }
  : VarSig ',' VarSigs        { $1 : $3 }
  | VarSig                    { [$1] }

VarSig :: { (Id, Kind) }
  : VAR ':' Kind              { (mkId $ symString $1, $3) }


Kind :: { Kind }
  : Kind '->' Kind            { KFun $1 $3 }
  | VAR                       { KVar (mkId $ symString $1) }
  | CONSTR                    { case constrString $1 of
                                  "Type"      -> KType
                                  "Coeffect"  -> KCoeffect
                                  "Predicate" -> KConstraint Predicate
                                  "Constraint" -> KConstraint InterfaceC
                                  s          -> kConstr $ mkId s }
  | '(' TyJuxt TyAtom ')'     { KPromote (TyApp $2 $3) }
  | TyJuxt TyAtom             { KPromote (TyApp $1 $2) }


Type :: { Type }
  : TyJuxt                    { $1 }
  | Type '->' Type            { FunTy $1 $3 }
  | Type '×' Type             { TyApp (TyApp (TyCon $ mkId ",") $1) $3 }
  | TyAtom '[' Coeffect ']'   { Box $3 $1 }
  | TyAtom '[' ']'            { Box (CInterval (CZero extendedNat) infinity) $1 }

  | TyAtom '<' Effect '>'     { Diamond $3 $1 }

TyApp :: { Type }
 : TyJuxt TyAtom              { TyApp $1 $2 }
 | TyAtom                     { $1 }

TyJuxt :: { Type }
  : TyJuxt '`' TyAtom '`'     { TyApp $3 $1 }
  | TyJuxt TyAtom             { TyApp $1 $2 }
  | TyAtom                    { $1 }
  | TyAtom '+' TyAtom         { TyInfix ("+") $1 $3 }
  | TyAtom '-' TyAtom         { TyInfix "-" $1 $3 }
  | TyAtom '*' TyAtom         { TyInfix ("*") $1 $3 }
  | TyAtom '^' TyAtom         { TyInfix ("^") $1 $3 }
  | TyAtom "∧" TyAtom         { TyInfix ("∧") $1 $3 }
  | TyAtom "∨" TyAtom         { TyInfix ("∨") $1 $3 }

Constraint :: { Type }
  : InterfaceConstraint { $1 }
  | PredicateConstraint { $1 }

PredicateConstraint :: { Type }
  : TyAtom '>' TyAtom         { TyInfix (">") $1 $3 }
  | TyAtom '<' TyAtom         { TyInfix ("<") $1 $3 }
  | TyAtom '>=' TyAtom        { TyInfix (">=") $1 $3 }
  | TyAtom '<=' TyAtom        { TyInfix ("<=") $1 $3 }
  | TyAtom '=' TyAtom         { TyInfix ("=") $1 $3 }
  | TyAtom '/=' TyAtom        { TyInfix ("/=") $1 $3 }

InterfaceConstraint :: { TConstraint }
  : CONSTR TyParams { foldl TyApp (TyCon . mkId . constrString $ $1) $2 }

TyAtom :: { Type }
  : TyAtomWithSpan { fst $1 }

TyAtomWithSpan :: { (Type, Span) }
  : CONSTR                    {
    % mkSpan (getPosToSpan $1) >>=
      \sp -> return (TyCon $ mkId $ constrString $1, sp) }
  | VAR                       {
    % mkSpan (getPosToSpan $1) >>=
      \sp -> return (TyVar (mkId $ symString $1), sp) }
  | INT                       {
    % mkSpan (getPosToSpan $1) >>=
      \sp -> return (let TokenInt _ x = $1 in TyInt x, sp) }
  | '(' Type ')'              {
    % mkSpan (getPos $1, getPos $3) >>=
      \sp -> return ($2, sp) }
  | '(' Type ',' Type ')'     {
    % mkSpan (getPos $1, getPos $5) >>=
      \sp -> return (TyApp (TyApp (TyCon $ mkId ",") $2) $4, sp) }

TyParams :: { [Type] }
  : TyAtom TyParams           { $1 : $2 } -- use right recursion for simplicity -- VBL
  |                           { [] }

Coeffect :: { Coeffect }
  : INT                         { let TokenInt _ x = $1 in CNat x }
  | '∞'                         { infinity }
  | FLOAT                       { let TokenFloat _ x = $1 in CFloat $ myReadFloat x }
  | CONSTR                      { case (constrString $1) of
                                    "Public" -> Level publicRepresentation
                                    "Private" -> Level privateRepresentation
                                    "Inf" -> infinity
                                    x -> error $ "Unknown coeffect constructor `" <> x <> "`" }
  | VAR                         { CVar (mkId $ symString $1) }
  | Coeffect ".." Coeffect      { CInterval $1 $3 }
  | Coeffect '+' Coeffect       { CPlus $1 $3 }
  | Coeffect '*' Coeffect       { CTimes $1 $3 }
  | Coeffect '-' Coeffect       { CMinus $1 $3 }
  | Coeffect '^' Coeffect       { CExpon $1 $3 }
  | Coeffect "∧" Coeffect       { CMeet $1 $3 }
  | Coeffect "∨" Coeffect       { CJoin $1 $3 }
  | '(' Coeffect ')'            { $2 }
  | '{' Set '}'                 { CSet $2 }
  | Coeffect ':' Type           { normalise (CSig $1 $3) }

Set :: { [(String, Type)] }
  : VAR ':' Type ',' Set      { (symString $1, $3) : $5 }
  | VAR ':' Type              { [(symString $1, $3)] }

Effect :: { Effect }
  : Effs                 { $1 }
  | {-empty-}            { [] }

Effs :: { [String] }
  : Eff ',' Effs              { $1 : $3 }
  | Eff                       { [$1] }

Eff :: { String }
  : CONSTR                    { constrString $1 }

Expr :: { Expr () () }
  : let LetBind MultiLet
      {% let (_, pat, mt, expr) = $2
      	in (mkSpan (getPos $1, getEnd $3)) >>=
           \sp -> return $ App sp ()
                   (Val (getSpan $3) () (Abs () pat mt $3)) expr
      }

  | '\\' '(' PAtom ':' Type ')' '->' Expr
      {% (mkSpan (getPos $1, getEnd $8)) >>=
             \sp -> return $ Val sp () (Abs () $3 (Just $5) $8) }

  | '\\' PAtom '->' Expr
      {% (mkSpan (getPos $1, getEnd $4)) >>=
             \sp -> return $ Val sp () (Abs () $2 Nothing $4) }

  | let LetBindEff MultiLetEff
      {% let (_, pat, mt, expr) = $2
        in (mkSpan (getPos $1, getEnd $3)) >>=
              \sp -> return $ LetDiamond sp () pat mt expr $3 }

  | case Expr of Cases
    {% (mkSpan (getPos $1, lastSpan $4)) >>=
             \sp -> return $ Case sp () $2 $4 }

  | if Expr then Expr else Expr
    {% do
        span1 <- mkSpan (getPos $1, getEnd $6)
        span2 <- mkSpan $ getPosToSpan $3
        span3 <- mkSpan $ getPosToSpan $3
        return $ Case span1 () $2
                  [(PConstr span2 () (mkId "True") [], $4),
                     (PConstr span3 () (mkId "False") [], $6)] }

  | Form
    { $1 }

LetBind :: { (Pos, Pattern (), Maybe Type, Expr () ()) }
  : PAtom ':' Type '=' Expr
      { (getStart $1, $1, Just $3, $5) }
  | PAtom '=' Expr
      { (getStart $1, $1, Nothing, $3) }

MultiLet :: { Expr () () }
MultiLet
  : ';' LetBind MultiLet
    {% let (_, pat, mt, expr) = $2

     	in (mkSpan (getPos $1, getEnd $3)) >>=
           \sp -> return $ App sp ()
     	               (Val (getSpan $3) () (Abs () pat mt $3)) expr }
  | in Expr
    { $2 }

LetBindEff :: { (Pos, Pattern (), Maybe Type, Expr () ()) }
  : PAtom '<-' Expr            { (getStart $1, $1, Nothing, $3) }
  | PAtom ':' Type '<-' Expr   { (getStart $1, $1, Just $3, $5) }

MultiLetEff :: { Expr () () }
MultiLetEff
  : ';' LetBindEff MultiLetEff
      {% let (_, pat, mt, expr) = $2
	      in (mkSpan (getPos $1, getEnd $3)) >>=
             \sp -> return $ LetDiamond sp () pat mt expr $3
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
  : Form '+' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () "+" $1 $3 }
  | Form '-' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () "-" $1 $3 }
  | Form '*' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () "*" $1 $3 }
  | Form '<' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () "<" $1 $3 }
  | Form '>' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () ">" $1 $3 }
  | Form OP  Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () (symString $2) $1 $3 }
  | Juxt           { $1 }

Juxt :: { Expr () () }
  : Juxt '`' Atom '`'         {% (mkSpan (getStart $1, getEnd $3)) >>= \sp -> return $ App sp () $3 $1 }
  | Juxt Atom                 {% (mkSpan (getStart $1, getEnd $2)) >>= \sp -> return $ App sp () $1 $2 }
  | Atom                      { $1 }

Atom :: { Expr () () }
  : '(' Expr ')'              { $2 }
  | INT                       {% let (TokenInt _ x) = $1
                                 in (mkSpan $ getPosToSpan $1)
                                    >>= \sp -> return $ Val sp () $ NumInt x }

  | FLOAT                     {% let (TokenFloat _ x) = $1
                                 in (mkSpan $ getPosToSpan $1)
                                     >>= \sp -> return $ Val sp () $ NumFloat $ read x }

  | VAR                       {% (mkSpan $ getPosToSpan $1)  >>= \sp -> return $ Val sp () $ Var () (mkId $ symString $1) }

  | '[' Expr ']'              {% (mkSpan (getPos $1, getPos $3)) >>= \sp -> return $ Val sp () $ Promote () $2 }
  | CONSTR                    {% (mkSpan $ getPosToSpan $1)  >>= \sp -> return $ Val sp () $ Constr () (mkId $ constrString $1) [] }
  | '(' Expr ',' Expr ')'     {% do
                                    span1 <- (mkSpan (getPos $1, getPos $5))
                                    span2 <- (mkSpan (getPos $1, getPos $3))
                                    span3 <- (mkSpan $ getPosToSpan $3)
                                    return $ App span1 () (App span2 ()
                                              (Val span3 () (Constr () (mkId ",") []))
                                                $2)
                                              $4 }
  | CHAR                      {% (mkSpan $ getPosToSpan $1) >>= \sp ->
                                  return $ Val sp () $
                                     case $1 of (TokenCharLiteral _ c) -> CharLiteral c }
  | STRING                    {% (mkSpan $ getPosToSpan $1) >>= \sp ->
                                  return $ Val sp () $
                                      case $1 of (TokenStringLiteral _ c) -> StringLiteral c }

{

mkSpan :: (Pos, Pos) -> ReaderT String (Either String) Span
mkSpan (start, end) = do
  filename <- ask
  return $ Span start end filename

parseError :: [Token] -> ReaderT String (Either String) a
parseError [] = lift $ Left "Premature end of file"
parseError t  =  lift . Left $ show l <> ":" <> show c <> ": parse error"
  where (l, c) = getPos (head t)

parseDefs :: FilePath -> String -> Either String (AST () ())
parseDefs file input = runReaderT (defs $ scanTokens input) file

parseAndDoImportsAndFreshenDefs :: (?globals :: Globals) => String -> IO (AST () ())
parseAndDoImportsAndFreshenDefs input = do
    ast <- parseDefsAndDoImports input
    return $ freshenAST ast

parseDefsAndDoImports :: (?globals :: Globals) => String -> IO (AST () ())
parseDefsAndDoImports input = do
    defs <- either die return $ parseDefs (sourceFilePath ?globals) input
    importedDefs <- forM imports $ \path -> do
      src <- readFile path
      let ?globals = ?globals { sourceFilePath = path }
      parseDefsAndDoImports src
    let allDefs = merge $ defs : importedDefs
    checkNameClashes allDefs
    checkMatchingNumberOfArgs allDefs
    return allDefs

  where
    merge :: [AST () ()] -> AST () ()
    merge xs =
      let conc [] dds defs ifaces insts = AST dds defs ifaces insts
          conc ((AST dds defs ifaces insts):xs) ddsAcc defsAcc ifacesAcc instsAcc =
            conc xs (dds <> ddsAcc) (defs <> defsAcc)
                    (ifaces <> ifacesAcc) (insts <> instsAcc)
       in conc xs [] [] [] []

    imports = map ((includePath ?globals </>) . (<> ".gr") . replace '.' '/')
              . mapMaybe (stripPrefix "import ") . lines $ input

    replace from to = map (\c -> if c == from then to else c)

    checkMatchingNumberOfArgs ds@(AST dataDecls defs ifaces insts) =
      mapM checkMatchingNumberOfArgs' defs

    checkMatchingNumberOfArgs' (Def _ name eqs _) =
      if length eqs >= 1
      then if (and $ map (\x -> x == head lengths) lengths)
            then return ()
            else
              die $ "Syntax error: Number of arguments differs in the equattypeConstructorns of "
                  <> sourceName name
      else return ()
        where
          lengths = map (\(Equation _ _ pats _) -> length pats) eqs


    checkNameClashes ds@(AST dataDecls defs ifaces insts) =
        if null clashes
	        then return ()
          else die $ "Error: Name clash: " <> intercalate ", " (map sourceName clashes)
      where
        clashes = names \\ nub names
        names = (`map` dataDecls) (\(DataDecl _ name _ _ _) -> name)
                <> (`map` defs) (\(Def _ name _ _) -> name)

lastSpan [] = fst $ nullSpanLocs
lastSpan xs = getEnd . snd . last $ xs

lastSpan' [] = fst $ nullSpanLocs
lastSpan' xs = endPos $ getSpan (last xs)

myReadFloat :: String -> Rational
myReadFloat str =
    case readFloat str of
      ((n, []):_) -> n
      _ -> error "Invalid number"

fst3 (a, b, c) = a
snd3 (a, b, c) = b
thd3 (a, b, c) = c
}
