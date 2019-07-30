module Language.Granule.Codegen.Emit.LowerType where
import Language.Granule.Codegen.Emit.MkId
import Language.Granule.Codegen.ClosureFreeDef
import Language.Granule.Syntax.Type
import Language.Granule.Codegen.Emit.Types
import LLVM.AST.Type

llvmTypeForEnvironment :: ClosureEnvironmentType -> IrType
llvmTypeForEnvironment (TyClosureEnvironment captureTypes) =
    StructureType {
        isPacked = False,
        elementTypes = map llvmType captureTypes }

llvmTypeForFunction :: IrType -> IrType -> IrType
llvmTypeForFunction paramType returnType =
    FunctionType returnType argumentTypes isVarArg
    where argumentTypes = [ptr i8, paramType]
          isVarArg = False

llvmTypeForClosure :: IrType -> IrType
llvmTypeForClosure functionType =
    StructureType {
        isPacked = False,
        elementTypes = [ptr functionType, ptr i8] }

{-|
A function type can be resolved to two different types
depending on the context. e.g. for
@
    Int -> Int -> Int
@
If it is a parameter type / return value it should be
@
    {{i32(i8*, i32), u8*}(i8*, i32), i8*}
@
If it is a definition type it should be
@
    {i32(i8*, i32), u8*}(i8*, i32)
@
For the former use `llvmSubType`, for the latter use `llvmTopLevelType`
|-}
llvmType :: GrType -> IrType
llvmType (FunTy from to) =
    llvmTypeForClosure $ llvmTypeForFunction (llvmType from) (llvmType to)
llvmType (TyApp (TyApp (TyCon (MkId "(,)")) left) right) =
    StructureType False [llvmType left, llvmType right]
llvmType (TyCon (MkId "Int")) = i32
llvmType (TyCon (MkId "Float")) = double
llvmType (TyCon (MkId "Char")) = i8
llvmType (TyCon (MkId "Handle")) = i8
llvmType (TyCon (MkId "Bool")) = i1
llvmType (Box coeffect ty) = llvmType ty
llvmType ty = error $ "Cannot lower the type " ++ show ty

llvmTopLevelType :: GrType -> IrType
llvmTopLevelType (FunTy from to) = llvmTypeForFunction (llvmType from) (llvmType to)
llvmTopLevelType other = llvmType other
