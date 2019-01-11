module Language.Granule.Codegen.BuildAST where
import Language.Granule.Codegen.NormalisedDef
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

lit :: Int -> Value ev Type
lit n = NumInt n

arg :: String -> Type -> Pattern Type
arg name ty = (PVar nullSpanNoFile ty (mkId name))

tts :: Type -> TypeScheme
tts ty = Forall nullSpanNoFile [] ty

app :: Expr () Type -> Expr () Type -> Expr () Type
app f x =
    App nullSpanNoFile retTy f x
    where (FunTy _ retTy) = annotation f

defval :: String -> Expr ev Type -> TypeScheme -> ValueDef ev Type
defval name initexpr ts =
    ValueDef nullSpanNoFile (mkId name) initexpr ts

defun :: String -> Pattern Type -> Expr () Type -> TypeScheme -> FunctionDef () Type
defun name arg bodyexpr ts =
    FunctionDef nullSpanNoFile (mkId name) bodyexpr arg ts

def :: String -> [Pattern Type] -> Expr () Type -> TypeScheme -> Def () Type
def name args bodyexpr ts =
    Def nullSpanNoFile (mkId name) [equation] ts
    where equation = Equation nullSpanNoFile ty args bodyexpr
          (Forall _ [] ty) = ts

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
