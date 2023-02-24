{
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Language.Granule.Syntax.Parser where

import Control.Arrow (second)
import Control.Monad (forM, when, unless)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Class (lift)
import Data.Char (isSpace)
import Data.Foldable (toList)
import Data.List (intercalate, nub, stripPrefix)
import Data.Maybe (mapMaybe)
import Data.Set (Set, (\\), fromList, insert, empty, singleton)
import qualified Data.Map as M
import Numeric
import System.FilePath ((</>), takeBaseName)
import System.Exit
import System.Directory (doesFileExist)

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

%name topLevel TopLevel
%name expr Expr
%name tscheme TypeScheme
%tokentype { Token }
%error { parseError }
%monad { StateT [Extension] (ReaderT String (Either String)) }

%token
    nl    { TokenNL _ }
    data  { TokenData _ }
    where { TokenWhere _ }
    module { TokenModule _ }
    hiding { TokenHiding _ }
    let   { TokenLet _ }
    in    { TokenIn  _  }
    if    { TokenIf _ }
    then  { TokenThen _ }
    else  { TokenElse _ }
    case  { TokenCase _ }
    spec  { TokenSpec _ }
    of    { TokenOf _ }
    try    { TokenTry _ }
    as    { TokenAs _ }
    catch    { TokenCatch _ }
    import { TokenImport _ _ }
    language { TokenPragma _ _ }
    clone { TokenCopy _ }
    endorse { TokenEndorse _ }
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
    '<='  { TokenLesserEq _ }
    '>='  { TokenGreaterEq _ }
    '|'   { TokenPipe _ }
    '_'   { TokenUnderscore _ }
    ';'   { TokenSemicolon _ }
    '.'   { TokenPeriod _ }
    '`'   { TokenBackTick _ }
    '^'   { TokenCaret _ }
    '%'   { TokenPercent _ }
    '..'  { TokenDotDot _ }
    "\\/" { TokenJoin _ }
    "/\\" { TokenMeet _ }
    '∘'   { TokenRing _ }
    '?'   { TokenEmptyHole _ }
    '{!'  { TokenHoleStart _ }
    '!}'  { TokenHoleEnd _ }
    '@'   { TokenAt _ }
    '!'   { TokenBang _ }
    '&'   { TokenBorrow _ }
    '#'   { TokenHash _ }
    '*{'  { TokenStar _ }

%right '∘'
%right in
%right '->'
%left ':'
%right '×'
%left '..'
%left '+' '-'
%left '*'
%left '&'
%left '^'
%left '|'
%left '.'
%%

TopLevel :: { AST () () }
  : module CONSTR where NL Defs
            { $5 { moduleName = Just $ mkId $ constrString $2 } }

  | module CONSTR hiding '(' Ids ')' where  NL Defs
            { let modName = mkId $ constrString $2
              in $9 { moduleName = Just modName, hiddenNames = $5 modName } }

  | language CONSTR NL TopLevel                     {% case parseExtensions (constrString $2) of
                                                    Just ext -> do
                                                       -- modify (\st -> st { globalsExtensions = ext : globalsExtensions st })
                                                       modify (\st -> ext : st)
                                                       return $4
                                                    Nothing -> error ("Unknown language extension " ++ symString $2)
                                                }

  | Defs                                        { $1 }

Ids :: { Id -> M.Map Id Id }
 : CONSTR          { \modName -> M.insert (mkId $ constrString $1) modName M.empty }
 | CONSTR ',' Ids  { \modName -> M.insert (mkId $ constrString $1) modName ($3 modName) }

Defs :: { AST () () }
  : Def                       { AST [] [$1] mempty mempty Nothing }
  | DataDecl                  { AST [$1] [] mempty mempty Nothing }
  | Import                    { AST [] [] (singleton $1) mempty Nothing }
  | DataDecl NL Defs          { $3 { dataTypes = $1 : dataTypes $3 } }
  | Def NL Defs               { $3 { definitions = $1 : definitions $3 } }
  | Import NL Defs            { $3 { imports = insert $1 (imports $3) } }

NL :: { () }
  : nl NL                     { }
  | nl                        { }

Import :: { Import }
  : import                    { let TokenImport _ ('i':'m':'p':'o':'r':'t':path) = $1
                                in dropWhile isSpace path <> ".gr"
                              }

Def :: { Def () () }
  : Sig NL Bindings
      {%  let name = fst3 $1 in
          case $3 of
            (nameB, _) | not (nameB == name) ->
              error $ "Name for equation `" <> nameB <> "` does not match the signature head `" <> name <> "`"

            (_, bindings) -> do
              span <- mkSpan (thd3 $1, endPos $ getSpan $ last (equations bindings))
              return $ Def span (mkId name) False Nothing bindings (snd3 $1)
      }
  | Sig NL Spec NL Bindings
      {%  let name = fst3 $1 in
          let spec = $3 in
          case $5 of
            (nameB, _) | not (nameB == name) ->
              error $ "Name for equation `" <> nameB <> "` does not match the signature head `" <> name <> "`"

            (_, bindings) -> do
              span <- mkSpan (thd3 $1, endPos $ getSpan $ last (equations bindings))
              return $ Def span (mkId name) False spec bindings (snd3 $1)
      }
  
Spec :: { Maybe (Spec () ()) }
  : spec SpecList           { let (exs, auxs)  = $2 in
                                         Just $ Spec nullSpanNoFile False exs auxs }

SpecList :: { ([Example () ()], [(Id, Maybe Type)]) }
  : Example ';' SpecList            { let (exs, auxs) = $3
                                           in ($1 : exs, auxs) }  
  | Components                          {   let auxs = $1
                                           in ([], auxs) }
  | {- empty -}                         { ([], []) }

Example :: { Example () () }
  : Expr '=' Expr                 { Example $1 $3 }

Components :: { [(Id, Maybe Type)] }
  : VAR                                   {% return [(mkId $ symString $1, Nothing)] }
  | VAR '%' Coeffect                   {% return [(mkId $ symString $1, Just $3)] }
  -- : VAR '[' Coeffect ']'                 {% return [(mkId $ symString $1, Just $3)] }
  | VAR ',' Components                   { (mkId $ symString $1, Nothing) : $3 }
  | VAR '%' Coeffect ',' Components  { (mkId $ symString $1, Just $3) : $5 }
  -- | VAR '[' Coeffect ']' ',' Components  { (mkId $ symString $1, Just $3) : $6 }
  | {- empty -}                           {% return [] }

DataDecl :: { DataDecl }
  : data CONSTR TyVars KindAnn where DataConstrs
      {% do
          span <- mkSpan (getPos $1, lastSpan' $6)
          return $ DataDecl span (mkId $ constrString $2) $3 $4 $6 }
  | data CONSTR TyVars KindAnn '=' DataConstrs
      {% do
          span <- mkSpan (getPos $1, lastSpan' $6)
          return $ DataDecl span (mkId $ constrString $2) $3 $4 $6 }

Sig :: { (String, TypeScheme, Pos) }
  : VAR ':' TypeScheme        { (symString $1, $3, getPos $1) }

Bindings :: { (String, EquationList () ()) }
  : Binding ';' NL Bindings   { let (v, bind) = $1
                                in case $4 of
                                    (v', binds)
                                      | v' == v ->
                                          (v, consEquation bind binds)
                                      | otherwise ->
                                          error $ "Identifier " <> show v' <> " in group of equations does not match " <> show v
                              }
  | Binding                   { case $1 of (v, bind) -> (v, EquationList (equationSpan bind) (mkId v) False [bind]) }

Binding :: { (String, Equation () ()) }
  : VAR '=' Expr
      {% do
          span <- mkSpan (getPos $1, getEnd $3)
          return (symString $1, Equation span (mkId $ symString $1) () False [] $3) }

  | VAR Pats '=' Expr
      {% do
          span <- mkSpan (getPos $1, getEnd $4)
          return (symString $1, Equation span (mkId $ symString $1) () False $2 $4) }

-- this was probably a silly idea @buggymcbugfix
  -- | '|' Pats '=' Expr
  --     {% do
  --         span <- mkSpan (getPos $1, getEnd $4)
  --         return (Nothing, Equation span () False $2 $4) }

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
  | VAR TyVars                  { (mkId $ symString $1, Type 0) : $2 }
  | {- empty -}                 { [] }

KindAnn :: { Maybe Kind }
  : ':' Kind                  { Just $2 }
  | {- empty -}               { Nothing }

Pats :: { [Pattern ()] }
  : PAtom                     { [$1] }
  | PAtom Pats                { $1 : $2 }

PAtom :: { Pattern () }
  : VAR
       {% (mkSpan $ getPosToSpan $1) >>= \sp -> return $ PVar sp () False (mkId $ symString $1) }

  | '_'
       {% (mkSpan $ getPosToSpan $1) >>= \sp -> return $ PWild sp () False }

  | INT
       {% (mkSpan $ getPosToSpan $1) >>= \sp -> return $ let TokenInt _ x = $1 in PInt sp () False x }

  | FLOAT
       {% (mkSpan $ getPosToSpan $1) >>= \sp -> return $ let TokenFloat _ x = $1 in PFloat sp () False $ read x }

  | CONSTR
       {% (mkSpan $ getPosToSpan $1) >>= \sp -> return $ let TokenConstr _ x = $1 in PConstr sp () False (mkId x) [] }

  | '(' NAryConstr ')'        { $2 }

  | '[' PAtom ']'
       {% (mkSpan (getPos $1, getPos $3)) >>= \sp -> return $ PBox sp () False $2 }

  | '!' PAtom
       {% (mkSpan (getPos $1, getPos $1)) >>= \sp -> return $ PBox sp () False $2 }

  | '[' NAryConstr ']'
       {% (mkSpan (getPos $1, getPos $3)) >>= \sp -> return $ PBox sp () False $2 }

  | '(' PMolecule ',' PMolecule ')'
       {% (mkSpan (getPos $1, getPos $5)) >>= \sp -> return $ PConstr sp () False (mkId ",") [$2, $4] }

PMolecule :: { Pattern () }
  : NAryConstr                { $1 }
  | PAtom                     { $1 }

NAryConstr :: { Pattern () }
  : CONSTR Pats               {% let TokenConstr _ x = $1
                                in (mkSpan (getPos $1, getEnd $ last $2)) >>=
                                       \sp -> return $ PConstr sp () False (mkId x) $2 }

ForallSig :: { [(Id, Kind)] }
 : '{' VarSigs '}' { $2 }
 | Vars1   { flip concatMap $1 (\id -> let k = mkId ("_k" <> id)
                                       in [(mkId id, TyVar k)]) }

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

 | '{' Constraints '}' '=>' Type
       {% mkSpan (getPos $1, getPos $4) >>= \sp -> return $ Forall sp [] $2 $5 }

VarSigs :: { [(Id, Kind)] }
  : VarSig ',' VarSigs        { $1 <> $3 }
  | VarSig                    { $1 }

VarSig :: { [(Id, Kind)] }
  : Vars1 ':' Kind            { map (\id -> (mkId id, $3)) $1 }
  | Vars1                     { flip concatMap $1 (\id -> let k = mkId ("_k" <> id)
                                                          in [(mkId id, TyVar k)]) }

-- A non-empty list of variables
Vars1 :: { [String] }
  : VAR                       { [symString $1] }
  | VAR Vars1                 { symString $1 : $2 }

Hint :: { (String, Int) }
  : '-' VAR                      { (symString $2, 0) } 
  | '-' VAR INT                  { let TokenInt _ x  = $3 in (symString $2, x) }

Hints :: { [(String, Int)] } 
  : Hint                      { [$1] }
  | Hint Hints                { $1 : $2 }

Kind :: { Kind }
  : Type                           { $1 }

Type :: { Type }
  : '(' VAR ':' Type ')' '->' Type { FunTy (Just . mkId . symString $ $2) Nothing $4 $7 }
  | '(' VAR ':' Type ')' '%' Coeffect '->' Type { FunTy (Just . mkId . symString $ $2) (Just $7) $4 $9 } 
  | TyJuxt                         { $1 }
  | '!' TyAtom                     { Box (TyCon $ mkId "Many") $2 }
  | '*' TyAtom                     { Star (TyCon $ mkId "Unique") $2 }
  | Type '->' Type                 { FunTy Nothing Nothing $1 $3 }
  | Type '%' Coeffect '->' Type    { FunTy Nothing (Just $3) $1 $5 }
  | Type '×' Type                  { TyApp (TyApp (TyCon $ mkId ",") $1) $3 }
  | Type '&' Type                  { TyApp (TyApp (TyCon $ mkId "&") $1) $3 }
  | TyAtom '[' Coeffect ']'        { Box $3 $1 }
  | TyAtom '*{' Guarantee '}'      { Star $3 $1 }
  | TyAtom '[' ']'                 { Box (TyInfix TyOpInterval (TyGrade (Just extendedNat) 0) infinity) $1 }
  | TyAtom '<' Effect '>'          { Diamond $3 $1 }
  | case Type of TyCases { TyCase $2 $4 }

TyApp :: { Type }
 : TyJuxt TyAtom              { TyApp $1 $2 }
 | TyAtom                     { $1 }

TyJuxt :: { Type }
  : TyJuxt '`' TyAtom '`'     { TyApp $3 $1 }
  | TyJuxt TyAtom             { TyApp $1 $2 }
  | TyAtom                    { $1 }
  | TyAtom '+' TyAtom         { TyInfix TyOpPlus $1 $3 }
  | TyAtom '-' TyAtom         { TyInfix TyOpMinus $1 $3 }
  | TyAtom '*' TyAtom         { TyInfix TyOpTimes $1 $3 }
  | TyAtom '^' TyAtom         { TyInfix TyOpExpon $1 $3 }
  | TyAtom "/\\" TyAtom       { TyInfix TyOpMeet $1 $3 }
  | TyAtom "\\/" TyAtom       { TyInfix TyOpJoin $1 $3 }
  | TyAtom '<=' TyAtom        { TyInfix TyOpLesserEq $1 $3 }
  | TyAtom '.' '<=' TyAtom    { TyInfix TyOpLesserEqNat $1 $4 }
  | TyAtom '>=' TyAtom        { TyInfix TyOpGreaterEq $1 $3 }
  | TyAtom '.' '>=' TyAtom    { TyInfix TyOpGreaterEqNat $1 $4 }
  | TyAtom '==' TyAtom        { TyInfix TyOpEq $1 $3 }
  | TyAtom '/=' TyAtom        { TyInfix TyOpNotEq $1 $3 }
  | TyAtom '=>' TyAtom        { TyInfix TyOpImpl $1 $3 }



TyCases :: { [(Type, Type)] }
 : TyCase TyCasesNext             { $1 : $2 }

TyCasesNext :: { [(Type, Type)] }
  : ';' TyCases                 { $2 }
  | {- empty -}               { [] }

TyCase :: { (Type, Type) }
  : Type '->' Type           { ($1, $3) }

Constraint :: { Type }
  : TyJuxt TyAtom             { TyApp $1 $2 }
  | TyAtom '>' TyAtom         { TyInfix TyOpGreaterNat $1 $3 }
  | TyAtom '<' TyAtom         { TyInfix TyOpLesserNat $1 $3 }
  | TyAtom '<=' TyAtom        { TyInfix TyOpLesserEq $1 $3 }
  | TyAtom '.' '<=' TyAtom    { TyInfix TyOpLesserEqNat $1 $4 }
  | TyAtom '>=' TyAtom        { TyInfix TyOpGreaterEq $1 $3 }
  | TyAtom '.' '>=' TyAtom    { TyInfix TyOpGreaterEqNat $1 $4 }
  | TyAtom '==' TyAtom        { TyInfix TyOpEq $1 $3 }
  | TyAtom '/=' TyAtom        { TyInfix TyOpNotEq $1 $3 }
  | TyAtom '=>' TyAtom        { TyInfix TyOpImpl $1 $3 }


TyAtom :: { Type }
  : CONSTR                    { case constrString $1 of
                                  "Type"      -> Type 0
                                  "Semiring"  -> kcoeffect
                                  s          -> tyCon s }
  | '(' ',' ')'               { TyCon $ mkId "," }
  | VAR                       { TyVar (mkId $ symString $1) }
  | INT                       { let TokenInt _ x = $1 in TyGrade Nothing x }
  | FLOAT                     { let TokenFloat _ x = $1 in TyRational $ myReadFloat x }
  -- | '.' INT                   { let TokenInt _ x = $2 in TyInt x }
  | '(' Type ')'              { $2 }
  | '(' Type ',' Type ')'     { TyApp (TyApp (TyCon $ mkId ",") $2) $4 }
  | TyAtom ':' Kind           { TySig $1 $3 }
  | '{' CoeffSet '}'              { TySet Normal $2 }
  | '{' CoeffSet '}' '.'          { TySet Opposite $2 }

TyParams :: { [Type] }
  : TyAtom TyParams           { $1 : $2 } -- use right recursion for simplicity -- VBL
  |                           { [] }

-- TODO: For maximum flexibility, Coeffect needs to be merged into TyAtom I think.
Coeffect :: { Coeffect }
  : INT                           { let TokenInt _ x = $1 in TyGrade Nothing x }
  | '.' INT                       { let TokenInt _ x = $2 in TyInt x }
  | '∞'                           { infinity }
  | FLOAT                         { let TokenFloat _ x = $1 in TyRational $ myReadFloat x }
  | CONSTR                        { case (constrString $1) of
                                      "Inf" -> infinity
                                      x -> TyCon $ mkId x }
  | VAR                           { TyVar (mkId $ symString $1) }
  | Coeffect '..' Coeffect        { TyInfix TyOpInterval $1 $3 }
  | Coeffect '+' Coeffect         { TyInfix TyOpPlus $1 $3 }
  | Coeffect '*' Coeffect         { TyInfix TyOpTimes $1 $3 }
  | Coeffect '-' Coeffect         { TyInfix TyOpMinus $1 $3 }
  | Coeffect '^' Coeffect         { TyInfix TyOpExpon $1 $3 }
  | Coeffect "/\\" Coeffect       { TyInfix TyOpMeet $1 $3 }
  | Coeffect "\\/" Coeffect       { TyInfix TyOpJoin $1 $3 }
  | '(' Coeffect ')'              { $2 }
  | '{' CoeffSet '}'              { TySet Normal $2 }
  | '{' CoeffSet '}' '.'          { TySet Opposite $2 }
  | Coeffect ':' Kind             { TySig $1 $3 }
  | '(' Coeffect ',' ',' Coeffect ')' { TyApp (TyApp (TyCon $ mkId ",,") $2) $5 }
  | '(' Coeffect '×' Coeffect ')'     { TyApp (TyApp (TyCon $ mkId ",,") $2) $4 }

CoeffSet :: { [Type] }
  : CoeffSetElems       { $1 }
  |                     { [] }

CoeffSetElems :: { [Type] }
  : CoeffSetElem ',' CoeffSetElems  { $1 : $3 }
  | CoeffSetElem                    { [$1] }

CoeffSetElem :: { Type }
  : CONSTR      { TyCon $ mkId $ constrString $1 }
  | VAR         { TyVar $ mkId $ symString $1 }


Effect :: { Type }
  : '{' EffSet '}'            { TySet Normal $2 }
  | {- EMPTY -}               { TyCon $ mkId "Pure" }
  | TyJuxt                    { $1 }

EffSet :: { [Type] }
  : Eff ',' EffSet         { $1 : $3 }
  | Eff                    { [$1] }

Eff :: { Type }
  : CONSTR                  { TyCon $ mkId $ constrString $1 }

Guarantee :: { Type }
  : CONSTR                  { TyCon $ mkId $ constrString $1 }

Expr :: { Expr () () }
  : let LetBind MultiLet
      {% let (_, pat, mt, expr) = $2
      	in (mkSpan (getPos $1, getEnd $3)) >>=
           \sp -> return $ App sp () False
                   (Val (getSpan $3) () False (Abs () pat mt $3)) expr
      }

  | '\\' '(' PAtom ':' Type ')' '->' Expr
      {% (mkSpan (getPos $1, getEnd $8)) >>=
             \sp -> return $ Val sp () False (Abs () $3 (Just $5) $8) }

  | '\\' PAtom '->' Expr
      {% (mkSpan (getPos $1, getEnd $4)) >>=
             \sp -> return $ Val sp () False (Abs () $2 Nothing $4) }

  | let LetBindEff MultiLetEff
      {% let (_, pat, mt, expr) = $2
        in (mkSpan (getPos $1, getEnd $3)) >>=
              \sp -> return $ LetDiamond sp () False pat mt expr $3 }

  | try Expr as '[' PAtom ']' in Expr catch Expr
      {% let e1 = $2; pat = $5; mt = Nothing; e2 = $8; e3 = $10
        in (mkSpan (getPos $1, getEnd $10)) >>=
              \sp -> return $ TryCatch sp () False e1 pat mt e2 e3 }
  | try Expr as '[' PAtom ']' ':' Type in Expr catch Expr
      {% let e1 = $2; pat = $5; mt = Just $8; e2 = $10; e3 = $12
        in (mkSpan (getPos $1, getEnd $12)) >>=
              \sp -> return $ TryCatch sp () False e1 pat mt e2 e3 }

  | case Expr of Cases
    {% (mkSpan (getPos $1, lastSpan $4)) >>=
             \sp -> return $ Case sp () False $2 $4 }

  | if Expr then Expr else Expr
    {% do
        span1 <- mkSpan (getPos $1, getEnd $6)
        span2 <- mkSpan $ getPosToSpan $3
        span3 <- mkSpan $ getPosToSpan $3
        return $ Case span1 () False $2
                  [(PConstr span2 () False (mkId "True") [], $4),
                     (PConstr span3 () False (mkId "False") [], $6)] }

  | clone Expr as CopyBind in Expr
    {% let t1 = $2; (_, pat, mt) = $4; t2 = $6 
      in (mkSpan (getPos $1, getEnd $6)) >>=
        \sp -> return $ App sp () False (App sp () False 
          (Val sp () False (Var () (mkId "uniqueBind"))) 
          (Val sp () False (Abs () pat mt t2))) t1 }

  | endorse Expr as CopyBind in Expr
    {% let t1 = $2; (_, pat, mt) = $4; t2 = $6 
      in (mkSpan (getPos $1, getEnd $6)) >>=
        \sp -> return $ App sp () False (App sp () False 
          (Val sp () False (Var () (mkId "trustedBind"))) 
          (Val sp () False (Abs () pat mt t2))) t1 }

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

CopyBind :: { (Pos, Pattern (), Maybe Type) }
  : PAtom ':' Type
    { (getStart $1, $1, Just $3) }
  | PAtom
    { (getStart $1, $1, Nothing) }

MultiLet :: { Expr () () }
MultiLet
  : ';' LetBind MultiLet
    {% let (_, pat, mt, expr) = $2

     	in (mkSpan (getPos $1, getEnd $3)) >>=
           \sp -> return $ App sp () False
     	               (Val (getSpan $3) () False (Abs () pat mt $3)) expr }
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
             \sp -> return $ LetDiamond sp () False pat mt expr $3
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
  : Form '+' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () False OpPlus $1 $3 }
  | Form '-' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () False OpMinus $1 $3 }
  | Form '*' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () False OpTimes $1 $3 }
  | Form '/' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () False OpDiv $1 $3 }
  | Form '<' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () False OpLesser $1 $3 }
  | Form '>' Form  {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () False OpGreater $1 $3 }
  | Form '<=' Form {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () False OpLesserEq $1 $3 }
  | Form '>=' Form {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () False OpGreaterEq $1 $3 }
  | Form '==' Form {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () False OpEq $1 $3 }
  | Form '/=' Form {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Binop sp () False OpNotEq $1 $3 }
  | Form '∘'  Form {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ App sp () False (App sp () False (Val sp () False (Var () (mkId "compose"))) $1) $3 }
  | Form '.'  Form {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ App sp () False (App sp () False (Val sp () False (Var () (mkId "compose"))) $1) $3 }
  | Juxt           { $1 }

Juxt :: { Expr () () }
  : Juxt '`' Atom '`'         {% (mkSpan (getStart $1, getEnd $3)) >>= \sp -> return $ App sp () False $3 $1 }
  | Juxt Atom                 {% (mkSpan (getStart $1, getEnd $2)) >>= \sp -> return $ App sp () False $1 $2 }
  | Atom                      { $1 }
  | Juxt '@' TyAtom           {% (mkSpan (getStart $1, getEnd $1)) >>= \sp -> return $ AppTy sp () False $1 $3 } -- TODO: span is not very accurate here

Hole :: { Expr () () }
  : '{!' Vars1 '!}'           {% (mkSpan (fst . getPosToSpan $ $1, second (+2) . snd . getPosToSpan $ $3)) >>= \sp -> return $ Hole sp () False (map mkId $2) Nothing }
  | '{!' Hints '!}'           {% (mkSpan (fst . getPosToSpan $ $1, second (+2) . snd . getPosToSpan $ $3)) >>= \sp -> return $ Hole sp () False [] (Just $ parseHints $2) }
  | '{!' Hints Vars1 '!}'     {% (mkSpan (fst . getPosToSpan $ $1, second (+2) . snd . getPosToSpan $ $4)) >>= \sp -> return $ Hole sp () False (map mkId $3) (Just $ parseHints $2) }
  | '{!' Vars1 Hints '!}'     {% (mkSpan (fst . getPosToSpan $ $1, second (+2) . snd . getPosToSpan $ $4)) >>= \sp -> return $ Hole sp () False (map mkId $2) (Just $ parseHints $3) }
  | '{!' '!}'                 {% (mkSpan (fst . getPosToSpan $ $1, second (+2) . snd . getPosToSpan $ $2)) >>= \sp -> return $ Hole sp () False [] Nothing }
  | '?'                       {% (mkSpan (fst . getPosToSpan $ $1, second (+1) . snd . getPosToSpan $ $1)) >>= \sp -> return $ Hole sp () False [] Nothing }

Atom :: { Expr () () }
  : '(' Expr ')'              { $2 }
  | INT                       {% let (TokenInt _ x) = $1
                                 in (mkSpan $ getPosToSpan $1)
                                    >>= \sp -> return $ Val sp () False $ NumInt x }
  -- | '<' Expr '>'              {% (mkSpan (getPos $1, getPos $3)) >>= \sp -> return $ App sp () False (Val sp () (Var () (mkId "pure"))) $2 }
  | FLOAT                     {% let (TokenFloat _ x) = $1
                                 in (mkSpan $ getPosToSpan $1)
                                     >>= \sp -> return $ Val sp () False $ NumFloat $ read x }

  | VAR                       {% (mkSpan $ getPosToSpan $1)  >>= \sp -> return $ Val sp () False $ Var () (mkId $ symString $1) }

  | '[' Expr ']'              {% (mkSpan (getPos $1, getPos $3)) >>= \sp -> return $ Val sp () False $ Promote () $2 }
  | '#' INT                   {% let (TokenInt _ x) = $2
                                 in (mkSpan $ getPosToSpan $1)
                                    >>= \sp -> return $ Val sp () False $ Nec () (Val sp () False $ NumInt x) }
  | '#' FLOAT                 {% let (TokenFloat _ x) = $2
                                 in (mkSpan $ getPosToSpan $1)
                                    >>= \sp -> return $ Val sp () False $ Nec () (Val sp () False $ NumFloat $ read x) }                                                                                           
  | CONSTR                    {% (mkSpan $ getPosToSpan $1)  >>= \sp -> return $ Val sp () False $ Constr () (mkId $ constrString $1) [] }
  | '#' CONSTR                {% (mkSpan $ getPosToSpan $2) >>= \sp -> return $ Val sp () False $ Nec () (Val sp () False $ Constr () (mkId $ constrString $2) [])}
  | '(' Expr ',' Expr ')'     {% do
                                    span1 <- (mkSpan (getPos $1, getPos $5))
                                    span2 <- (mkSpan (getPos $1, getPos $3))
                                    span3 <- (mkSpan $ getPosToSpan $3)
                                    return $ App span1 () False (App span2 () False
                                              (Val span3 () False (Constr () (mkId ",") []))
                                                $2)
                                              $4 }
  | CHAR                      {% (mkSpan $ getPosToSpan $1) >>= \sp ->
                                  return $ Val sp () False $
                                     case $1 of (TokenCharLiteral _ c) -> CharLiteral c }
  | STRING                    {% (mkSpan $ getPosToSpan $1) >>= \sp ->
                                  return $ Val sp () False $
                                      case $1 of (TokenStringLiteral _ c) -> StringLiteral c }
  | '#' CHAR                  {% (mkSpan $ getPosToSpan $1) >>= \sp ->
                                  return $ Val sp () False $
                                     case $2 of (TokenCharLiteral _ c) -> Nec () (Val sp () False $ CharLiteral c) }
  | '#' STRING                {% (mkSpan $ getPosToSpan $1) >>= \sp ->
                                  return $ Val sp () False $
                                     case $2 of (TokenStringLiteral _ c) -> Nec () (Val sp () False $ StringLiteral c) }                              
  | Hole                      { $1 }
  | '&' Expr                  {% (mkSpan $ getPosToSpan $1) >>= \sp -> return $ App sp () False (Val sp () False (Var () (mkId "uniqueReturn"))) $2 }

{

mkSpan :: (Pos, Pos) -> StateT [Extension] (ReaderT String (Either String)) Span
mkSpan (start, end) = do
  filename <- lift $ ask
  return $ Span start end filename

parseError :: [Token] -> StateT [Extension] (ReaderT String (Either String)) a
parseError [] = lift $ lift $ Left "Premature end of file"
parseError t = do
    file <- lift $ ask
    lift $ lift $ Left $ file <> ":" <> show l <> ":" <> show c <> ": parse error"
  where (l, c) = getPos (head t)

parseDefs :: FilePath -> String -> Either String (AST () (), [Extension])
parseDefs file input = runReaderT (runStateT (topLevel $ scanTokens input) []) file

parseHints :: [(String, Int)] -> Hints
parseHints hints = 
  Hints {
    hSubtractive = ("s", 0) `elem` hints,
    hPruning     = ("p", 0) `elem` hints,
    hNoTimeout   = ("nt", 0) `elem` hints,
    hGradeOnRule = ("g", 0) `elem` hints,
    hTimeout     = lookup "t" hints,
    hIndex       = lookup "i" hints
  }

parseAndDoImportsAndFreshenDefs :: (?globals :: Globals) => String -> IO (AST () (), [Extension])
parseAndDoImportsAndFreshenDefs input = do
    (ast, extensions) <- parseDefsAndDoImports input
    return (freshenAST ast, extensions)

parseAndFreshenDefs :: (?globals :: Globals) => String -> IO (AST () (), [Extension])
parseAndFreshenDefs input = do
  (ast, extensions) <- either failWithMsg return $ parseDefs sourceFilePath input
  return (freshenAST ast, extensions)

parseDefsAndDoImports :: (?globals :: Globals) => String -> IO (AST () (), [Extension])
parseDefsAndDoImports input = do
    (ast, extensions) <- either failWithMsg return $ parseDefs sourceFilePath input
    case moduleName ast of
      Nothing -> doImportsRecursively (imports ast) (ast { imports = empty }, extensions)
      Just (Id name _) ->
        if name == takeBaseName sourceFilePath
          then doImportsRecursively (imports ast) (ast { imports = empty }, extensions)
          else do
            failWithMsg $ "Module name `" <> name <> "` does not match filename `" <> takeBaseName sourceFilePath <> "`"

  where
    -- Get all (transitive) dependencies. TODO: blows up when the file imports itself
    doImportsRecursively :: Set Import -> (AST () (), [Extension]) -> IO (AST () (), [Extension])
    doImportsRecursively todo (ast@(AST dds defs done hidden name), extensions) = do
      case toList (todo \\ done) of
        [] -> return (ast, extensions)
        (i:todo) -> do
          fileLocal <- doesFileExist i
          let path = if fileLocal then i else includePath </> i
          let ?globals = ?globals { globalsSourceFilePath = Just path } in do

            src <- readFile path
            (AST dds' defs' imports' hidden' _, extensions') <- either failWithMsg return $ parseDefs path src
            doImportsRecursively
              (fromList todo <> imports')
              (AST (dds' <> dds) (defs' <> defs) (insert i done) (hidden `M.union` hidden') name, extensions ++ extensions')

failWithMsg :: String -> IO a
failWithMsg msg = putStrLn msg >> exitFailure

lastSpan [] = fst $ nullSpanLocs
lastSpan xs = getEnd . snd . last $ xs

lastSpan' [] = fst $ nullSpanLocs
lastSpan' xs = endPos $ getSpan (last xs)

myReadFloat :: String -> Rational
myReadFloat str =
    case readFloat str of
      ((n, []):_) -> n
      _ -> error "Invalid number"

}
