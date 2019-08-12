module Language.Granule.Codegen.Emit.Names where
import Language.Granule.Syntax.Identifiers
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
