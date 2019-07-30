module Language.Granule.Codegen.BuildAST where
import Language.Granule.Codegen.NormalisedDef
import Language.Granule.Codegen.MarkGlobals
import Language.Granule.Codegen.ClosureFreeDef
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Annotated

int :: Type
int = TyCon (mkId "Int")

val :: Value ev Type -> Expr ev Type
val v = Val nullSpanNoFile ty v
        where ty = annotation v

var :: String -> Type -> Value ev Type
var ident ty = Var ty (mkId ident)

gvar :: String -> Type -> Value GlobalMarker Type
gvar ident ty = Ext ty $ GlobalVar ty (mkId ident)

gcfvar :: String -> Type -> ClosureFreeValue
gcfvar ident ty = Ext ty $ Left $ GlobalVar ty (mkId ident)

lit :: Int -> Value ev Type
lit n = NumInt n

arg :: String -> Type -> Pattern Type
arg name ty = (PVar nullSpanNoFile ty (mkId name))

pint :: Int -> Pattern Type
pint n = PInt nullSpanNoFile int n

tts :: Type -> TypeScheme
tts ty = Forall nullSpanNoFile [] [] ty

app :: Expr ev Type -> Expr ev Type -> Expr ev Type
app f x =
    App nullSpanNoFile retTy f x
    where (FunTy _ retTy) = annotation f

defval :: String -> Expr ev Type -> TypeScheme -> ValueDef ev Type
defval name initexpr ts =
    ValueDef nullSpanNoFile (mkId name) initexpr ts

defun :: String -> Pattern Type -> Expr ev Type -> TypeScheme -> FunctionDef ev Type
defun name arg bodyexpr ts =
    FunctionDef nullSpanNoFile (mkId name) bodyexpr arg ts

def :: String -> [Pattern Type] -> Expr ev Type -> TypeScheme -> Def ev Type
def name args bodyexpr ts =
    Def nullSpanNoFile (mkId name) [equation] ts
    where equation = Equation nullSpanNoFile ty args bodyexpr
          (Forall _ [] _ ty) = ts

casedef :: String -> [([Pattern Type], Expr ev Type)] -> TypeScheme -> Def ev Type
casedef name cases ts =
    Def nullSpanNoFile (mkId name) (equation <$> cases) ts
    where equation (args, bodyexpr) = Equation nullSpanNoFile ty args bodyexpr
          (Forall _ [] _ ty) = ts

caseexpr :: Expr ev Type -> [(Pattern Type, Expr ev Type)] -> Expr ev Type
caseexpr swexp cases@((p,ex):_) =
    Case nullSpanNoFile ty swexp cases
    where ty = annotation ex

ppair :: Pattern Type -> Pattern Type -> Pattern Type
ppair left right =
    PConstr nullSpanNoFile ty (mkId "(,)") [left, right]
    where ty = pairType (annotation left) (annotation right)

lambdaexp :: Pattern Type -> Type -> Expr ev Type -> Expr ev Type
lambdaexp argument fnty body =
    Val nullSpanNoFile fnty (Abs fnty argument Nothing body)

plus :: Expr ev Type -> Expr ev Type -> Expr ev Type
x `plus` y
    | xTy == yTy =
        Binop nullSpanNoFile xTy "+" x y
    | otherwise =
        error $ show xTy ++ " not equal to " ++ show yTy
    where (xTy, yTy) = (annotation x, annotation y)

normASTFromDefs :: [FunctionDef ev Type] -> [ValueDef ev Type] -> NormalisedAST ev Type
normASTFromDefs functionDefs valueDefs = NormalisedAST [] functionDefs valueDefs
