module Language.Granule.Codegen.MarkGlobals where
import Language.Granule.Codegen.NormalisedDef
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Data.Bifunctor.Foldable

data GlobalMarker =
    GlobalVar Type Id
    deriving (Show, Eq)

instance Pretty GlobalMarker where
    prettyL l (GlobalVar _ x) = prettyL 0 x

markGlobals :: NormalisedAST () Type -> NormalisedAST GlobalMarker Type
markGlobals (NormalisedAST dataDecls functionDefs valueDefs) =
    let globals = (definitionIdentifier <$> functionDefs) ++ (definitionIdentifier <$> valueDefs)
        functionDefs' = map (markGlobalsInFunctionDef globals) functionDefs
        valueDefs'    = map (markGlobalsInValueDef globals) valueDefs
    in NormalisedAST dataDecls functionDefs' valueDefs'

markGlobalsInFunctionDef :: [Id] -> FunctionDef () Type -> FunctionDef GlobalMarker Type
markGlobalsInFunctionDef globals def@FunctionDef { functionDefBody = body } =
    def { functionDefBody = markGlobalsInExpr globals body }

markGlobalsInValueDef :: [Id] -> ValueDef () Type -> ValueDef GlobalMarker Type
markGlobalsInValueDef globals def@ValueDef { valueDefInitializer = initializer } =
    def { valueDefInitializer = markGlobalsInExpr globals initializer }

markGlobalsInExpr :: [Id] -> Expr () Type -> Expr GlobalMarker Type
markGlobalsInExpr globals =
    bicata fixMapExtExpr markInValue
    where markInValue (VarF ty ident)
              | ident `elem` globals = Ext ty (GlobalVar ty ident)
              | otherwise = Var ty ident
          markInValue other =
              fixMapExtValue (\ty ev -> error "Extension value in AST before global marking.") other

fixMapExtExpr :: ExprF eva a (Expr evb a) (Value evb a) -> Expr evb a
fixMapExtExpr (AppF sp ty fn arg) = App sp ty fn arg
fixMapExtExpr (BinopF sp ty op lhs rhs) = Binop sp ty op lhs rhs
fixMapExtExpr (LetDiamondF sp ty pat mty now next) = LetDiamond sp ty pat mty now next
fixMapExtExpr (ValF sp ty val) = Val sp ty val
fixMapExtExpr (CaseF sp ty swexp arms) = Case sp ty swexp arms

fixMapExtValue :: (a -> eva -> Value evb a)
               -> ValueF eva a (Value evb a) (Expr evb a)
               -> Value evb a
fixMapExtValue f (VarF ty ident) = Var ty ident
fixMapExtValue f (AbsF ty pat mty body) = Abs ty pat mty body
fixMapExtValue f (PromoteF ty ex) = Promote ty ex
fixMapExtValue f (PureF ty ex) = Pure ty ex
fixMapExtValue f (ConstrF ty ident vals) = Constr ty ident vals
fixMapExtValue f (NumIntF n) = NumInt n
fixMapExtValue f (NumFloatF n) = NumFloat n
fixMapExtValue f (CharLiteralF ch) = CharLiteral ch
fixMapExtValue f (StringLiteralF txt) = StringLiteral txt
fixMapExtValue f (ExtF ty ev) = f ty ev
