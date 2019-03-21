module Language.Granule.Codegen.Emit.LowerClosure where

import Control.Monad (zipWithM_)
import Data.Maybe (fromJust)

import Language.Granule.Codegen.Emit.Types (IrType, GrType)
import Language.Granule.Codegen.Emit.LowerType (llvmTypeForEnvironment, llvmTopLevelType, llvmType)
import Language.Granule.Codegen.Emit.Names
import Language.Granule.Codegen.Emit.LLVMHelpers
import Language.Granule.Codegen.Emit.Primitives (malloc)
import Language.Granule.Codegen.ClosureFreeDef
import Language.Granule.Syntax.Identifiers (Id)

import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction
import LLVM.AST (mkName, Operand, Operand(..))
import LLVM.AST.Type (i8, ptr, Type(..))
import LLVM.AST.Constant (Constant)
import qualified LLVM.AST.Constant as C

emitEnvironmentType :: (MonadModuleBuilder m) => ClosureFreeFunctionDef -> m (Maybe IrType)
emitEnvironmentType (ClosureFreeFunctionDef { closureFreeDefEnvironment = envType }) =
    maybeEmitEnvironmentType envType

maybeEmitEnvironmentType :: (MonadModuleBuilder m)
                         => Maybe NamedClosureEnvironmentType
                         -> m (Maybe IrType)
maybeEmitEnvironmentType =
    mapM toLLVMType
    where toLLVMType (identifier, environmentType) =
              let llvmName = mkName identifier
                  llvmType = llvmTypeForEnvironment environmentType
              in typedef llvmName (Just llvmType)

emitClosureMarker :: (MonadIRBuilder m, MonadModuleBuilder m)
                  => GrType
                  -> Maybe Operand
                  -> ClosureMarker
                  -> m Operand
emitClosureMarker ty (Just env) (CapturedVar _ ident idx) =
    do
        addr <- gep env $ (ConstantOperand . intConstant) <$> [0, idx]
        load addr 4
emitClosureMarker _ Nothing (CapturedVar _ _ _) =
    error "Use of captured variable when no environment present."
emitClosureMarker ty maybeParentEnv (MakeClosure ident initializer) =
    do
        let (ClosureEnvironmentInit environmentTypeName variableInitializers) = initializer
        let environmentType = NamedTypeReference (mkName environmentTypeName)
        environmentVoidPtr <- mallocEnvironment environmentType
        environmentTypedPtr <- bitcast environmentVoidPtr (ptr environmentType)
        emitEnvironmentInit variableInitializers environmentTypedPtr maybeParentEnv
        emitClosureConstruction ident ty environmentVoidPtr
emitClosureMarker ty _ (MakeTrivialClosure identifier) =
    return $ ConstantOperand $ makeTrivialClosure identifier ty

emitEnvironmentInit :: (MonadModuleBuilder m, MonadIRBuilder m)
                    => [ClosureVariableInit]
                    -> Operand
                    -> Maybe Operand
                    -> m ()
emitEnvironmentInit variableInitializers env maybeParentEnv =
    zipWithM_ emitEnvironmentVariableInit [0..] variableInitializers
    where emitEnvironmentVariableInit n (FromParentEnv ident ty idx) =
              do
                  let parentEnv = fromJust maybeParentEnv
                  uninitAddr <- gep env $ (ConstantOperand . intConstant) <$> [0, n]
                  parentAddr <- gep parentEnv $ (ConstantOperand . intConstant) <$> [0, idx]
                  value <- load parentAddr 4
                  store uninitAddr 4 value
          emitEnvironmentVariableInit n (FromLocalScope ident ty) =
              do
                  uninitAddr <- gep env $ (ConstantOperand . intConstant) <$> [0, n]
                  let value = LocalReference (llvmType ty) (localNameFromId ident)
                  store uninitAddr 4 value

emitClosureConstruction :: (MonadIRBuilder m)
                        => Id
                        -> GrType
                        -> Operand
                        -> m Operand
emitClosureConstruction ident ty environmentPtr =
    do
        let closureType  = llvmType ty
        let undefClosure = ConstantOperand $ C.Undef closureType
        let functionPtr  = ConstantOperand $ makePointerToFunction ident ty
        closure  <- insertValue undefClosure functionPtr [0]
        closure' <- insertValue closure environmentPtr   [1]
        return closure'

makeTrivialClosure :: Id
                   -> GrType
                   -> Constant
makeTrivialClosure definitionIdentifier definitionType =
    C.Struct {
        C.structName = Nothing,
        C.isPacked = False,
        C.memberValues =
            [makePointerToFunction definitionIdentifier definitionType,
             C.Undef (ptr i8)] }

makePointerToFunction :: Id -> GrType -> Constant
makePointerToFunction definitionIdentifier definitionType =
    C.GlobalReference functionPointerType functionName
    where functionName        = functionNameFromId definitionIdentifier
          functionPointerType = ptr (llvmTopLevelType definitionType)

emitTrivialClosure :: (MonadModuleBuilder m)
                   => (Id, GrType)
                   -> m Operand
emitTrivialClosure (definitionIdentifier, definitionType) =
    global closureName closureType initializer
    where closureName = definitionNameFromId definitionIdentifier
          closureType = llvmType definitionType
          initializer = makeTrivialClosure definitionIdentifier definitionType

mallocEnvironment :: (MonadIRBuilder m) => IrType -> m Operand
mallocEnvironment ty =
    call (ConstantOperand malloc) [(ConstantOperand $ sizeOf ty, [])]
