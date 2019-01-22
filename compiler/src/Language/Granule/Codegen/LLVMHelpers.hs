module Language.Granule.Codegen.LLVMHelpers where

import Data.Traversable

import LLVM.AST
import LLVM.AST.Global
import LLVM.AST.Type
import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad
import Data.String (fromString)
import Data.Char (ord)
import LLVM.AST.Constant (Constant)
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.Linkage as L

-- | Define and emit a (non-variadic) internal function definition
privateFunction
  :: MonadModuleBuilder m
  => Name  -- ^ Function name
  -> [(Type, ParameterName)]  -- ^ Parameter types and name suggestions
  -> Type  -- ^ Return type
  -> ([Operand] -> IRBuilderT m ())  -- ^ Function body builder
  -> m Operand
privateFunction label argtys retty body = do
  let tys = fst <$> argtys
  (paramNames, blocks) <- runIRBuilderT emptyIRBuilder $ do
    paramNames <- forM argtys $ \(_, paramName) -> case paramName of
      NoParameterName -> fresh
      ParameterName p -> fresh `named` p
    body $ zipWith LocalReference tys paramNames
    return paramNames
  let
    def = GlobalDefinition functionDefaults
      { name        = label
      , parameters  = (zipWith (\ty nm -> Parameter ty nm []) tys paramNames, False)
      , returnType  = retty
      , basicBlocks = blocks
      , linkage     = L.Private
      }
    funty = ptr $ FunctionType retty (fst <$> argtys) False
  emitDefn def
  pure $ ConstantOperand $ C.GlobalReference funty label

mkPName :: String -> ParameterName
mkPName = ParameterName . fromString

sizeOf :: Type -> Constant
sizeOf ty = C.PtrToInt sizeAsPtr i64
            where sizeAsPtr = C.GetElementPtr {
                                  C.inBounds = True,
                                  C.address  = C.Null $ ptr ty,
                                  C.indices  = [C.Int 32 1] }

charConstant :: Char -> Constant
charConstant ch =
    C.Int {
        C.integerBits = 8,
        C.integerValue = toInteger (ord ch) }

stringConstant :: String -> Constant
stringConstant str =
    C.Vector (map charConstant str)
