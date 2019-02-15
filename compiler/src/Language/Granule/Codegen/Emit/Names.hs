module Language.Granule.Codegen.Emit.Names where
import Language.Granule.Syntax.Identifiers
import Language.Granule.Codegen.Emit.MkId
import Language.Granule.Syntax.Type
import LLVM.AST (Name, mkName)
import LLVM.IRBuilder.Module (ParameterName)
import Language.Granule.Codegen.Emit.LLVMHelpers

functionNameFromId :: Id -> Name
functionNameFromId identifier =
    mkName $ "fn." ++ internalName identifier

definitionNameFromId :: Id -> Name
definitionNameFromId identifier =
    mkName $ "def." ++ internalName identifier

localNameFromId :: Id -> Name
localNameFromId identifier =
    mkName $ "local." ++ internalName identifier

parameterNameFromId :: Id -> ParameterName
parameterNameFromId identifier =
    mkPName $ "local." ++ internalName identifier

mangleTypeName :: Type -> String
mangleTypeName (FunTy from to) =
    "fun." ++ (mangleTypeName from) ++ ".to." ++ (mangleTypeName to) ++ "#"
mangleTypeName (TyApp (TyApp (TyCon (MkId "(,)")) left) right) =
    "pair.#" ++ (mangleTypeName left) ++ ","
        ++ (mangleTypeName right) ++ "#"
mangleTypeName (TyCon (Id _ internal)) = internal
mangleTypeName (Box coeffect ty) = "box#" ++ (mangleTypeName ty)
