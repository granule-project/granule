{
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module Language.Granule.Syntax.Parser where

import Control.Monad (forM, when, unless)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class (lift)
import Data.Char (isSpace)
import Data.Foldable (toList)
import Data.List (intercalate, nub, stripPrefix)
import Data.Maybe (mapMaybe)
import Data.Set (Set, (\\), fromList, insert, singleton)
import Numeric
import System.FilePath ((</>))

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Lexer
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.FirstParameter (FirstParameter)
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
    import { TokenImport _ _ }
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
    '<='   { TokenLesserEq _ }
    '>='   { TokenGreaterEq _ }
    ','   { TokenComma _ }
    '×'   { TokenCross _ }
    '='   { TokenEq _ }
    '=='  { TokenEquiv _ }
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
    '|'   { TokenPipe _ }
    '_'   { TokenUnderscore _ }
    ';'   { TokenSemicolon _ }
    '.'   { TokenPeriod _ }
    '`'   { TokenBackTick _ }
    '^'   { TokenCaret _ }
    '..'  { TokenDotDot _ }
    "\\/" { TokenJoin _ }
    "/\\" { TokenMeet _ }
    '∘'   { TokenRing _ }

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

Defs :: { AST () () }
  : Def                       { AST [] [$1] [] [] mempty }

  | DataDecl                  { AST [$1] [] [] [] mempty }

  | DataDecl NL Defs          { let (AST dds defs ifaces insts imports) = $3
                                 in AST ($1 : dds) defs ifaces insts imports }

  | IFaceDecl                 { AST [] [] [$1] [] mempty }

  | IFaceDecl NL Defs         { let (AST dds defs ifaces insts imports) = $3
                                 in AST dds defs ($1 : ifaces) insts imports }

  | InstDecl                  { AST [] [] [] [$1] mempty }

  | InstDecl NL Defs          { let (AST dds defs ifaces insts imports) = $3
                                 in AST dds defs ifaces ($1 : insts) imports }

  | Def NL Defs               { let (AST dds defs ifaces insts imports) = $3
                                 in AST dds ($1 : defs) ifaces insts imports }

  | Import                    { AST [] [] [] [] (singleton $1) }

  | Import NL Defs            { let (AST dds defs ifaces insts imports) = $3
                                in AST dds defs ifaces insts (insert $1 imports) }

NL :: { () }
  : nl NL                     { }
  | nl                        { }

Import :: { Import }
  : import                    { let TokenImport _ ('i':'m':'p':'o':'r':'t':path) = $1
                                in dropWhile isSpace path <> ".gr"
                              }

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
  | '(' IFaceVarSig ')' { % mkSpan (getPos $1, getPos $3) >>= \sp -> return $ (sp, (fst $2, Just (snd $2))) }

IFaceVarSig :: { (Id, Kind) }
  : VAR ':' Kind { (mkId $ symString $1, $3) }

IFaceSigs :: { [InterfaceMethod] }
  : Sig ';' IFaceSigs
    { % mkSpan (thd3 $1, getEnd $ snd3 $1) >>= \sp -> return $ InterfaceMethod sp (mkId $ fst3 $1) (snd3 $1) : $3 }
  | Sig
    { % mkSpan (thd3 $1, getEnd $ snd3 $1) >>= \sp -> return $ [InterfaceMethod sp (mkId $ fst3 $1) (snd3 $1)] }

IFaceDecl :: { Interface }
  : interface IFaceName IFaceVars where IFaceSigs
  { % mkSpan (getPos $1, lastSpan' $5) >>= \sp -> return $ Interface sp $2 [] (snd $3) $5 }
  | interface IFaceConstrained IFaceName IFaceVars where IFaceSigs
  { % mkSpan (getPos $1, lastSpan' $6) >>= \sp -> return $ Interface sp $3 $2 (snd $4) $6 }
  | interface IFaceName IFaceVars
  { % mkSpan (getPos $1, endPos (fst $3)) >>= \sp -> return $ Interface sp $2 [] (snd $3) [] }
  | interface IFaceConstrained IFaceName IFaceVars
  { % mkSpan (getPos $1, endPos (fst $4)) >>= \sp -> return $ Interface sp $3 $2 (snd $4) [] }

InstBinds :: { [InstanceEquation () ()] }
  : NamedBinding ';' InstBindsRest
    { % mkSpan (snd $ fst $1, getEnd $ snd $1) >>= \sp -> return $ InstanceEquation sp (fmap mkId $ fst $ fst $1) (snd $1) : $3 }
  | NamedBinding
    { % mkSpan (snd $ fst $1, getEnd $ snd $1) >>= \sp -> return [InstanceEquation sp (fmap mkId $ fst $ fst $1) (snd $1)] }

InstBindsRest :: { [InstanceEquation () ()] }
  : Binding ';' InstBindsRest
    { % mkSpan (snd $ fst $1, getEnd $ snd $1) >>= \sp -> return $ InstanceEquation sp (fmap mkId $ fst $ fst $1) (snd $1) : $3 }
  | Binding
    { % mkSpan (snd $ fst $1, getEnd $ snd $1) >>= \sp -> return [InstanceEquation sp (fmap mkId $ fst $ fst $1) (snd $1)] }

InstTys :: { (Span, [Type]) }
  : InstTy InstTys { % mkSpan (getStart $1, getEnd $2) >>= \sp -> pure (sp, snd $1 : snd $2) }
  | InstTy { (fst $1, [snd $1]) }

InstTy :: { (Span, Type) }
  : TyAtomWithSpan { $1 }
  | '[' CoeffectWithSpan ']' { (fst $2, TyCoeffect (snd $2)) }

InstForm :: { InstanceTypes }
  : InstTys { InstanceTypes (fst $1) (snd $1) }

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

  | '(' PMolecule ',' PMolecule ')'
       {% (mkSpan (getPos $1, getPos $5)) >>= \sp -> return $ PConstr sp () (mkId ",") [$2, $4] }

PMolecule :: { Pattern () }
  : NAryConstr                { $1 }
  | PAtom                     { $1 }

NAryConstr :: { Pattern () }
  : CONSTR Pats               {% let TokenConstr _ x = $1
                                in (mkSpan (getPos $1, getEnd $ last $2)) >>=
                                       \sp -> return $ PConstr sp  () (mkId x) $2 }

ForallSig :: { [(Id, Kind)] }
 : '{' VarSigs '}' { $2 }
 | VarSigs         { $1 }

Forall :: { (((Pos, Pos), [(Id, Kind)]), [Type]) }
 : forall ForallSig '.'                          { (((getPos $1, getPos $3), $2), []) }
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
  : VarSig ',' VarSigs        { $1 <> $3 }
  | VarSig                    { $1 }

VarSig :: { [(Id, Kind)] }
  : Vars1 ':' Kind            { map (\id -> (mkId id, $3)) $1 }
  | Vars1                     { flip concatMap $1 (\id -> let k = mkId ("_k" <> id)
                                                          in [(mkId id, KVar k)]) }

-- A non-empty list of variables
Vars1 :: { [String] }
  : VAR                       { [symString $1] }
  | VAR Vars1                 { symString $1 : $2 }

Kind :: { Kind }
  : Kind '->' Kind            { KFun $1 $3 }
  | TyJuxt {
    case $1 of
      (TyCon c) -> case internalName c of
                     "Type"       -> KType
                     "Coeffect"   -> KCoeffect
                     "Predicate"  -> KConstraint Predicate
                     "Constraint" -> KConstraint InterfaceC
                     s            -> kConstr $ mkId s
      (TyVar v) -> KVar v
      t -> KPromote t
  }

TypeWithSpan :: { (Span, Type) }
  : TyJuxtWithSpan                  { $1 }
  | TypeWithSpan '->' TypeWithSpan  { % binaryType FunTy $1 $3 }
  | TypeWithSpan '×' TypeWithSpan   { % binaryType (\t1 t2 -> TyApp (TyApp (TyCon (mkId ",")) t1) t2) $1 $3 }
  | TyAtomWithSpan '[' Coeffect ']' { % mkBox $1 $3 $4 }
  | TyAtomWithSpan '[' ']'          { % mkBox $1 (CInterval (CZero extendedNat) infinity) $3 }
  | TyAtomWithSpan '<' Effect '>'   { % mkDiamond $1 $3 $4 }

Type :: { Type }
  : TypeWithSpan { snd $1 }

TyApp :: { Type }
 : TyJuxt TyAtom              { TyApp $1 $2 }
 | TyAtom                     { $1 }

TyJuxt :: { Type }
  : TyJuxtWithSpan { snd $1 }

TyJuxtWithSpan :: { (Span, Type) }
  : TyJuxtWithSpan '`' TyAtom '`'     { % withStartEndSndIsTok $1 $4 $ TyApp $3 (snd $1) }
  | TyJuxtWithSpan TyAtomWithSpan     { % binaryType TyApp $1 $2 }
  | TyAtomWithSpan                    { $1 }
  | TyAtomWithSpan '+' TyAtomWithSpan { % binaryType (TyInfix TyOpPlus) $1 $3 }
  | TyAtomWithSpan '-' TyAtomWithSpan { % binaryType (TyInfix TyOpMinus) $1 $3 }
  | TyAtomWithSpan '*' TyAtomWithSpan { % binaryType (TyInfix TyOpTimes) $1 $3 }
  | TyAtomWithSpan '^' TyAtomWithSpan { % binaryType (TyInfix TyOpExpon) $1 $3 }
  | TyAtomWithSpan "/\\" TyAtomWithSpan { % binaryType (TyInfix TyOpMeet) $1 $3 }
  | TyAtomWithSpan "\\/" TyAtomWithSpan { % binaryType (TyInfix TyOpJoin) $1 $3 }

Constraint :: { Type }
  : InterfaceConstraint { $1 }
  | PredicateConstraint { $1 }

PredicateConstraint :: { Type }
  : TyAtom '>' TyAtom         { TyInfix TyOpGreater $1 $3 }
  | TyAtom '<' TyAtom         { TyInfix TyOpLesser $1 $3 }
  | TyAtom '>=' TyAtom        { TyInfix TyOpGreaterEq $1 $3 }
  | TyAtom '<=' TyAtom        { TyInfix TyOpLesserEq $1 $3 }
  | TyAtom '=' TyAtom         { TyInfix TyOpEq $1 $3 }
  | TyAtom '/=' TyAtom        { TyInfix TyOpNotEq $1 $3 }

InterfaceConstraint :: { TConstraint }
  : CONSTR InstTys { foldl TyApp (TyCon . mkId . constrString $ $1) (snd $2) }

TyAtom :: { Type }
  : TyAtomWithSpan { snd $1 }

TyAtomWithSpan :: { (Span, Type) }
  : CONSTR                    {
    % mkSpan (getPosToSpan $1) >>=
      \sp -> return (sp, TyCon $ mkId $ constrString $1) }
  | VAR                       {
    % mkSpan (getPosToSpan $1) >>=
      \sp -> return (sp, TyVar (mkId $ symString $1)) }
  | INT                       {
    % mkSpan (getPosToSpan $1) >>=
      \sp -> return (sp, let TokenInt _ x = $1 in TyInt x) }
  | '(' Type ')'              {
    % mkSpan (getPos $1, getPos $3) >>=
      \sp -> return (sp, $2) }
  | '(' Type ',' Type ')'     {
    % mkSpan (getPos $1, getPos $5) >>=
      \sp -> return (sp, TyApp (TyApp (TyCon $ mkId ",") $2) $4) }

TyParams :: { [Type] }
  : TyAtom TyParams           { $1 : $2 } -- use right recursion for simplicity -- VBL
  |                           { [] }

CoeffectAtomWithSpan :: { (Span, Coeffect) }
  : INT
    { % withPosToSpan $1 $ let TokenInt _ x = $1 in CNat x }
  | '∞'
    { % withPosToSpan $1 infinity }
  | FLOAT
    { % withPosToSpan $1 $ let TokenFloat _ x = $1 in (CFloat $ myReadFloat x) }
  | CONSTR
    { % withPosToSpan $1 $
        case (constrString $1) of
          "Public" -> Level publicRepresentation
          "Private" -> Level privateRepresentation
          "Inf" -> infinity
          x -> error $ "Unknown coeffect constructor `" <> x <> "`" }
  | VAR
    { % mkSpan (getPosToSpan $1) >>= \sp -> pure (sp, CVar (mkId $ symString $1)) }
  | '(' Coeffect ')' { % withPos2 $1 $3 $2 }
  | '{' Set '}'      { % withPos2 $1 $3 (CSet $2) }

CoeffectWithSpan :: { (Span, Coeffect) }
  : CoeffectWithSpan '..' CoeffectWithSpan { % binaryCoeff CInterval $1 $3 }
  | CoeffectWithSpan '+'  CoeffectWithSpan { % binaryCoeff CPlus  $1 $3 }
  | CoeffectWithSpan '*'  CoeffectWithSpan { % binaryCoeff CTimes $1 $3 }
  | CoeffectWithSpan '-'  CoeffectWithSpan { % binaryCoeff CMinus $1 $3 }
  | CoeffectWithSpan '^'  CoeffectWithSpan { % binaryCoeff CExpon $1 $3 }
  | CoeffectWithSpan "/\\"  CoeffectWithSpan { % binaryCoeff CMeet  $1 $3 }
  | CoeffectWithSpan "\\/"  CoeffectWithSpan { % binaryCoeff CJoin  $1 $3 }
  | CoeffectWithSpan ':' TypeWithSpan  { % binaryCoeff (\x y -> normalise $ CSig x y) $1 $3 }
  | CoeffectAtomWithSpan { $1 }

Coeffect :: { Coeffect }
  : CoeffectWithSpan { snd $1 }

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
  | NAryConstr ':' Type '=' Expr
      { (getStart $1, $1, Just $3, $5) }
  | NAryConstr '=' Expr
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
  : Form '+' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () OpPlus $1 $3 }
  | Form '-' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () OpMinus $1 $3 }
  | Form '*' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () OpTimes $1 $3 }
  | Form '<' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () OpLesser $1 $3 }
  | Form '>' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () OpGreater $1 $3 }
  | Form '<=' Form {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () OpLesserEq $1 $3 }
  | Form '>=' Form {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () OpGreaterEq $1 $3 }
  | Form '==' Form {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () OpEq $1 $3 }
  | Form '/=' Form {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () OpNotEq $1 $3 }
  | Form '∘'  Form {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ App sp () (App sp () (Val sp () (Var () (mkId "compose"))) $1) $3 }
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
  -- | '<' Expr '>'              {% (mkSpan (getPos $1, getPos $3)) >>= \sp -> return $ App sp () (Val sp () (Var () (mkId "pure"))) $2 }
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
parseError t  =  do
    file <- ask
    lift . Left $ file <> ":" <> show l <> ":" <> show c <> ": parse error"
  where (l, c) = getPos (head t)

parseDefs :: FilePath -> String -> Either String (AST () ())
parseDefs file input = runReaderT (defs $ scanTokens input) file

parseAndDoImportsAndFreshenDefs :: (?globals :: Globals) => String -> IO (AST () ())
parseAndDoImportsAndFreshenDefs input = do
    ast <- parseDefsAndDoImports input
    return $ freshenAST ast

parseDefsAndDoImports :: (?globals :: Globals) => String -> IO (AST () ())
parseDefsAndDoImports input = do
    AST dds defs ifaces insts imports <- either error pure $ parseDefs sourceFilePath input
    doImportsRecursively imports (AST dds defs ifaces insts mempty)
  where
    -- Get all (transitive) dependencies. TODO: blows up when the file imports itself
    doImportsRecursively :: Set Import -> AST () () -> IO (AST () ())
    doImportsRecursively todo ast@(AST dds defs ifaces insts done) = do
      case toList (todo \\ done) of
        [] -> return ast
        (i:todo) ->
          let path = includePath </> i in
          let ?globals = ?globals { globalsSourceFilePath = Just path } in do
            src <- readFile path
            let AST dds' defs' ifaces' insts' imports' = either error id (parseDefs path src)
            doImportsRecursively
              (fromList todo <> imports')
              (AST (dds' <> dds) (defs' <> defs) (ifaces' <> ifaces) (insts' <> insts) (insert i done))

    -- the following check doesn't seem to be needed because this comes up during type checking @buggymcbugfix
    -- checkMatchingNumberOfArgs ds@(AST dataDecls defs) =
    --   mapM checkMatchingNumberOfArgs' defs

    -- checkMatchingNumberOfArgs' (Def _ name eqs _) =
    --     when (length eqs >= 1 && any (/= head lengths) lengths)
    --       ( error $ "Syntax error: Number of arguments differs in the equations of `"
    --         <> sourceName name <> "`"
    --       )
        -- where
        --   lengths = map (\(Equation _ _ pats _) -> length pats) eqs


lastSpan [] = fst $ nullSpanLocs
lastSpan xs = getEnd . snd . last $ xs

lastSpan' [] = fst $ nullSpanLocs
lastSpan' xs = endPos $ getSpan (last xs)

withStartEnd :: (FirstParameter a Span, FirstParameter b Span) => a -> b -> c -> ReaderT String (Either String) (Span, c)
withStartEnd x y c = fmap (,c) $ mkSpan (getStart x, getEnd y)
withStartEndSndIsTok x y c = fmap (,c) $ mkSpan (getStart x, getPos y)

withPosToSpan x c = fmap (,c) $ mkSpan (getPosToSpan x)
withPos2 x y c = fmap (,c) $ mkSpan (getPos x, getPos y)
binaryTerm f x y = withStartEnd x y (f (snd x) (snd y))
binaryTermSndIsTok f ty e tok = withStartEndSndIsTok ty tok (f e (snd ty))
binaryCoeff = binaryTerm
binaryType = binaryTerm
mkBox = binaryTermSndIsTok Box
mkDiamond = binaryTermSndIsTok Diamond

myReadFloat :: String -> Rational
myReadFloat str =
    case readFloat str of
      ((n, []):_) -> n
      _ -> error "Invalid number"

fst3 (a, b, c) = a
snd3 (a, b, c) = b
thd3 (a, b, c) = c
}
