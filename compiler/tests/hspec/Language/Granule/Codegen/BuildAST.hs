module Language.Granule.Codegen.AstBuilding where
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
val v = Val nullSpan ty v
        where ty = annotation v

var :: String -> Type -> Value ev Type
var ident ty = Var ty (mkId ident)

lit :: Int -> Value ev Type
lit n = NumInt n

arg :: String -> Type -> Pattern Type
arg name ty = (PVar nullSpan ty (mkId name))

tts :: Type -> TypeScheme
tts ty = Forall nullSpan [] ty

app :: Expr () Type -> Expr () Type -> Expr () Type
app f x =
    App nullSpan retTy f x
    where (FunTy _ retTy) = annotation f

defval :: String -> Expr () Type -> TypeScheme -> ValueDef () Type
defval name initexpr ts =
    ValueDef nullSpan (mkId name) initexpr ts

defun :: String -> [Pattern Type] -> Expr () Type -> TypeScheme -> Def () Type
defun name args bodyexpr ts =
    Def nullSpan (mkId name) bodyexpr args ts

lambdaexp :: Pattern Type -> Type -> Expr ev Type -> Expr ev Type
lambdaexp argument fnty body =
    Val nullSpan fnty (Abs fnty argument Nothing body)

plus :: Expr ev Type -> Expr ev Type -> Expr ev Type
x `plus` y | xTy == yTy =
    Binop nullSpan xTy "+" x y
    where (xTy, yTy) = (annotation x, annotation y)
