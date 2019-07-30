{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.Granule.Codegen.Emit.EmitLLVM where

import LLVM.AST.Type (i8, i32, i64, ptr, void)
--import LLVM.AST.Typed
import qualified LLVM.AST as IR
--import qualified LLVM.AST.Float as F

import LLVM.AST (Operand, mkName)
import LLVM.AST.Constant (Constant(..))
import qualified LLVM.AST.Constant as C
import LLVM.AST.Type hiding (Type)
import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction

import Language.Granule.Codegen.Emit.Types (GrType, IrType)
import Language.Granule.Codegen.Emit.LLVMHelpers
import Language.Granule.Codegen.Emit.EmitableDef
import Language.Granule.Codegen.Emit.EmitterState
import Language.Granule.Codegen.Emit.Names
import Language.Granule.Codegen.Emit.LowerClosure (emitEnvironmentType, emitTrivialClosure)
import Language.Granule.Codegen.Emit.LowerType (llvmTopLevelType, llvmType)
import Language.Granule.Codegen.Emit.LowerExpression (emitExpression)
import Language.Granule.Codegen.Emit.Primitives (writeInt)

import Language.Granule.Codegen.ClosureFreeDef
import Language.Granule.Codegen.NormalisedDef

import Language.Granule.Syntax.Pattern (boundVars, Pattern)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Def (DataDecl)
import Language.Granule.Syntax.Type hiding (Type)

import Data.String (fromString)
import qualified Data.Map.Strict as Map

import Control.Monad.Fix
import Control.Monad.State.Strict hiding (void)
--import Debug.Trace


externWriteInt :: (MonadModuleBuilder m) => m Operand
externWriteInt = do
  printf <- externVarArgs (mkName "printf") [ptr i8] i32
  function "writeInt" [(i32, mkPName "n")] void $ \[n] -> do
    _ <- globalStringPtr "%d\n" (mkName ".formatInt")
    let addr = IR.ConstantOperand $ C.GetElementPtr True formatStr [intConstant 0, intConstant 0]
               where formatStr = C.GlobalReference ty ".formatInt"
                     ty = ptr (ArrayType 4 i8)
    _ <- call printf [(addr, []), (n, [])]
    retVoid

emitLLVM :: String -> ClosureFreeAST -> Either String IR.Module
emitLLVM moduleName (ClosureFreeAST dataDecls functionDefs valueDefs) =
    let buildModule name m = evalState (buildModuleT name m) (EmitterState { localSymbols = Map.empty })
    in Right $ buildModule (fromString moduleName) $ do
        _ <- extern (mkName "malloc") [i64] (ptr i8)
        _ <- extern (mkName "abort") [] void
        _ <- externWriteInt

        mapM_ emitDataDecl dataDecls
        mapM_ emitEnvironmentType functionDefs
        mapM_ emitFunctionDef functionDefs
        valueInitPairs <- mapM emitValueDef valueDefs
        emitGlobalInitializer valueInitPairs

emitGlobalInitializer :: (MonadModuleBuilder m) => [(Operand, Operand)] -> m Operand
emitGlobalInitializer valueInitPairs =
    function (mkName "main") [] i32 $ \[] -> do
        mapM_ (\(global, initializer) -> do
            value <- call initializer []
            store global 4 value) valueInitPairs
        exitCode <- load (IR.ConstantOperand $ GlobalReference (ptr i32) (mkName "def.main")) 4
        _ <- call (IR.ConstantOperand writeInt) [(exitCode, [])]
        ret exitCode

emitValueDef :: MonadState EmitterState m
             => MonadModuleBuilder m
             => MonadFix m
             => ClosureFreeValueDef
             -> m (Operand, Operand)
emitValueDef def@(ValueDef sp ident initExpr typeScheme) =
    do
        clearLocals
        let name = definitionNameFromId ident
        let valueType = llvmTopLevelType (type_ def)
        let initializerName = mkName $ "init." ++ internalName ident
        initializer <- privateFunction initializerName [] valueType $ \[] -> do
            returnValue <- emitExpression Nothing initExpr
            ret returnValue
        value <- global name valueType (Undef valueType)
        return (value, initializer)
    where
      type_ ValueDef { valueDefTypeScheme = (Forall _ _ _ ty) } = ty

maybeEnvironment :: Maybe NamedClosureEnvironmentType -> Maybe IrType
maybeEnvironment = fmap (\(name, _) -> NamedTypeReference (mkName name))

emitFunctionDef :: (MonadState EmitterState m, MonadModuleBuilder m, MonadFix m)
                => ClosureFreeFunctionDef
                -> m (Operand, Operand)
emitFunctionDef def@(ClosureFreeFunctionDef sp ident environment body argument typeScheme) =
    do
        clearLocals
        let maybeEnvironmentType = maybeEnvironment environment -- maybeEmitEnvironmentType environment
        function <- emitFunction ident maybeEnvironmentType body argument (type_ def)
        trivialClosure <- emitTrivialClosure (ident, type_ def)
        return (trivialClosure, function)
    where
      type_ ClosureFreeFunctionDef { closureFreeDefTypeScheme = (Forall _ _ _ ty) } = ty

emitFunction :: (MonadState EmitterState m, MonadModuleBuilder m, MonadFix m)
             => Id
             -> Maybe IrType
             -> EmitableExpr
             -> Pattern GrType
             -> GrType
             -> m Operand
emitFunction ident maybeEnvironmentType body argument (FunTy from to) =
    do
        let parameterId = head $ boundVars argument
        let parameterName = parameterNameFromId parameterId
        let (parameterType, returnType) = (llvmType from, llvmType to)
        let parameter = (parameterType, parameterName)
        let environmentParameter = (ptr i8, mkPName "env")
        privateFunction
            (functionNameFromId ident)
            [environmentParameter, parameter] returnType $ \[env, param] -> do
                addLocal parameterId param
                typedEnvrionmentPointer <- maybeBitcastEnvironment env maybeEnvironmentType
                returnValue <- emitExpression typedEnvrionmentPointer body
                ret returnValue
emitFunction _ _ _ _ _ = error "cannot emit function with non function type"

maybeBitcastEnvironment :: (MonadIRBuilder m)
                        => Operand
                        -> Maybe IrType
                        -> m (Maybe Operand)
maybeBitcastEnvironment environmentPointerUntyped =
    traverse emitBitcast
    where
      emitBitcast environmentType =
        bitcast environmentPointerUntyped (ptr environmentType)

emitDataDecl :: {-(MonadModuleBuilder m) =>-} DataDecl -> m ()
emitDataDecl = error "Cannot emit data decls yet!"
