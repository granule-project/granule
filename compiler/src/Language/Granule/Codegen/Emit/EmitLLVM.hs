{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.Granule.Codegen.Emit.EmitLLVM where

import LLVM.AST.Type (i8, i32, i64, ptr, void)
import LLVM.AST (mkName)
--import LLVM.AST.Typed
import qualified LLVM.AST as IR
--import qualified LLVM.AST.Float as F

import LLVM.AST (Operand)
import LLVM.AST.Constant (Constant(..))
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

import Language.Granule.Codegen.ClosureFreeDef
import Language.Granule.Codegen.NormalisedDef

import Language.Granule.Syntax.Pattern (boundVars, Pattern)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type hiding (Type)
import Language.Granule.Syntax.Def

import Data.String (fromString)
import qualified Data.Map.Strict as Map

import Control.Exception (SomeException)
import Control.Monad.Fix
import Control.Monad.State.Strict hiding (void)
--import Debug.Trace




{-
makePairBuiltin :: (MonadModuleBuilder m) => Type -> m Operand
makePairBuiltin returnType@(TyApp (TyApp (TyCon (MkId "(,)")) left) right) =
    do
        let functionName = mkName $ "constr." ++ (mangleTypeName ty) ++ ".right"
        let functionName = mkName $ "constr." ++ (mangleTypeName ty) ++ ".left"
        let (leftType, rightType) = (llvmType left, llvmType right)

        makeSnd <- privateFunction [(ptr i8, mkPName "env"),
                         (rightType, mkPName "snd")]
                        (llvmType returnType) $ \[env, second] -> do
            leftVoidPtr <- mallocEnvironment leftType

        privateFunction [(ptr i8,    mkPName "env")
                         (leftType,  mkPName "fst")]
                         $ \[_, fstArg] -> do
            fstVoidPtr <- mallocEnvironment leftType
            fstPtr <- bitcast leftVoidPtr
            store fstPtr 4 fstArg

        {-let undefClosure = IR.ConstantOperand $ Undef closureType
        let functionPtr  = IR.ConstantOperand $ makePointerToFunction ident ty
            closure  <- insertValue undefClosure functionPtr [0]
            closure' <- insertValue closure environmentPtr   [1]
            ret (fstVoidPtr, makeSnd)-}

makePairBuiltin _ = error "Type is not a builtin pair"
-}



emitLLVM :: String -> ClosureFreeAST -> Either SomeException IR.Module
emitLLVM moduleName (ClosureFreeAST dataDecls functionDefs valueDefs) =
    let buildModule name m = evalState (buildModuleT name m) (EmitterState { localSymbols = Map.empty })
    in Right $ buildModule (fromString moduleName) $ do
        malloc <- extern (mkName "malloc") [i64] (ptr i8)
        abort <- extern (mkName "abort") [] void
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
        let valueType = llvmTopLevelType (definitionType def)
        let initializerName = mkName $ "init." ++ (internalName ident)
        initializer <- privateFunction initializerName [] valueType $ \[] -> do
            returnValue <- emitExpression Nothing initExpr
            ret returnValue
        value <- global name valueType (Undef valueType)
        return (value, initializer)

maybeEnvironment :: Maybe NamedClosureEnvironmentType -> Maybe IrType
maybeEnvironment = fmap (\(name, _) -> NamedTypeReference (mkName name))

emitFunctionDef :: (MonadState EmitterState m, MonadModuleBuilder m, MonadFix m)
                => ClosureFreeFunctionDef
                -> m (Operand, Operand)
emitFunctionDef def@(ClosureFreeFunctionDef sp ident environment body argument typeScheme) =
    do
        clearLocals
        let maybeEnvironmentType = maybeEnvironment environment -- maybeEmitEnvironmentType environment
        function <- emitFunction ident maybeEnvironmentType body argument (definitionType def)
        trivialClosure <- emitTrivialClosure (ident, definitionType def)
        return (trivialClosure, function)

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
maybeBitcastEnvironment environmentPointerUntyped maybeEnvironmentType =
    mapM emitBitcast maybeEnvironmentType
    where emitBitcast environmentType =
              bitcast environmentPointerUntyped (ptr environmentType)


emitDataDecl = error "Cannot emit data decls yet!"
