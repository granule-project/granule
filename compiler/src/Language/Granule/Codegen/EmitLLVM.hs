{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.Granule.Codegen.EmitLLVM where

import LLVM.AST.Type (i1, i8, i32, i64, double, ptr, void)
import LLVM.AST (mkName, Name)
--import LLVM.AST.Typed
import qualified LLVM.AST as IR
--import qualified LLVM.AST.Float as F
import LLVM.AST.Constant (Constant)
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.FloatingPointPredicate as FPP
import qualified LLVM.AST.IntegerPredicate as IP

import LLVM.AST (Operand)
import LLVM.AST.Type hiding (Type)
import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction
import qualified LLVM.IRBuilder.Constant as IC
import qualified LLVM.AST.Type as IRType

import Language.Granule.Codegen.LLVMHelpers
import Language.Granule.Codegen.ClosureFreeDef
import Language.Granule.Codegen.NormalisedDef
import Language.Granule.Codegen.MarkGlobals
import Language.Granule.Syntax.Pattern (boundVars, Pattern)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type hiding (Type)
import Language.Granule.Syntax.Type as GRType
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Annotated
import Language.Granule.Syntax.Pattern

import Data.Bifunctor.Foldable (bipara)
import Data.String (fromString)
import Data.Maybe (fromJust)
import Data.Text (unpack)
import Data.Foldable (foldrM)
import Data.Map.Strict hiding (map)
import qualified Data.Map.Strict as Map

import Control.Exception (SomeException)
import Control.Monad (zipWithM_)
import Control.Monad.Fix
import Control.Monad.State.Strict hiding (void)
--import Debug.Trace

type GrType = GRType.Type
type IrType = IRType.Type

type EmitableExpr = ClosureFreeExpr
type EmitableValue = ClosureFreeValue

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
pattern MkId s <- (internalName -> s) where
    MkId s = Id s s

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

mangleTypeName :: Type -> String
mangleTypeName (FunTy from to) =
    "fun#" ++ (mangleTypeName from) ++ "#to#" ++ (mangleTypeName to) ++ "#"
mangleTypeName (TyApp (TyApp (TyCon (MkId "(,)")) left) right) =
    "pair#" ++ (mangleTypeName leftPart) ++ "#,#"
        ++ (mangleTypeName rightPart) ++ "#"
mangleTypeName (TyCon (Id _ internal)) = internal
mangleTypeName (Box coeffect ty) = "box#" ++ (mangleTypeName ty)

makePairBuiltin :: (MonadModuleBuilder m) => Type -> m Operand
makePairBuiltin returnType@(TyApp (TyApp (TyCon (MkId "(,)")) left) right) =
    do
        let functionName = mkName $ "make#" ++ (mangleTypeName ty) ++ "#right"
        let functionName = mkName $ "make#" ++ (mangleTypeName ty) ++ "#left"
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

        {-let undefClosure = IR.ConstantOperand $ C.Undef closureType
        let functionPtr  = IR.ConstantOperand $ makePointerToFunction ident ty
            closure  <- insertValue undefClosure functionPtr [0]
            closure' <- insertValue closure environmentPtr   [1]
            ret (fstVoidPtr, makeSnd)-}


makePairBuiltin _ = error "Type is not a builtin pair"


llvmTopLevelType :: GrType -> IrType
llvmTopLevelType (FunTy from to) = llvmTypeForFunction (llvmType from) (llvmType to)
llvmTopLevelType other = llvmType other

maybeEmitEnvironmentType :: (MonadModuleBuilder m)
                         => Maybe NamedClosureEnvironmentType
                         -> m (Maybe IrType)
maybeEmitEnvironmentType =
    mapM toLLVMType
    where toLLVMType (identifier, environmentType) =
              let llvmName = mkName identifier
                  llvmType = llvmTypeForEnvironment environmentType
              in typedef llvmName (Just llvmType)


emitLLVM :: String -> ClosureFreeAST -> Either SomeException IR.Module
emitLLVM moduleName (ClosureFreeAST dataDecls functionDefs valueDefs) =
    let buildModule name m = evalState (buildModuleT name m) Map.empty
    in Right $ buildModule (fromString moduleName) $ do
        malloc <- extern (mkName "malloc") [i64] (ptr i8)
        abort <- extern (mkName "abort") [] void
        mapM_ emitDataDecl dataDecls
        mapM_ emitEnvironmentType functionDefs
        mapM_ emitFunctionDef functionDefs
        valueInitPairs <- mapM emitValueDef valueDefs
        emitGlobalInitializer valueInitPairs

emitEnvironmentType :: (MonadModuleBuilder m) => ClosureFreeFunctionDef -> m (Maybe IrType)
emitEnvironmentType (ClosureFreeFunctionDef { closureFreeDefEnvironment = envType }) =
    maybeEmitEnvironmentType envType


emitGlobalInitializer :: (MonadModuleBuilder m) => [(Operand, Operand)] -> m Operand
emitGlobalInitializer valueInitPairs =
    function (mkName "main") [] i32 $ \[] -> do
        mapM_ (\(global, initializer) -> do
            value <- call initializer []
            store global 4 value) valueInitPairs
        exitCode <- load (IR.ConstantOperand $ C.GlobalReference (ptr i32) (mkName "def.main")) 4
        ret exitCode

emitValueDef :: MonadState (Map Id Operand) m
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
        value <- global name valueType (C.Undef valueType)
        return (value, initializer)

maybeEnvironment :: Maybe NamedClosureEnvironmentType -> Maybe IrType
maybeEnvironment = fmap (\(name, _) -> NamedTypeReference (mkName name))

emitFunctionDef :: (MonadState (Map Id Operand) m, MonadModuleBuilder m, MonadFix m) => ClosureFreeFunctionDef -> m (Operand, Operand)
emitFunctionDef def@(ClosureFreeFunctionDef sp ident environment body argument typeScheme) =
    do
        clearLocals
        let maybeEnvironmentType = maybeEnvironment environment -- maybeEmitEnvironmentType environment
        function <- emitFunction ident maybeEnvironmentType body argument (definitionType def)
        trivialClosure <- emitTrivialClosure (ident, definitionType def)
        return (trivialClosure, function)

emitFunction :: (MonadState (Map Id Operand) m, MonadModuleBuilder m, MonadFix m)
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

maybeBitcastEnvironment :: (MonadIRBuilder m)
                        => Operand
                        -> Maybe IrType
                        -> m (Maybe Operand)
maybeBitcastEnvironment environmentPointerUntyped maybeEnvironmentType =
    mapM emitBitcast maybeEnvironmentType
    where emitBitcast environmentType =
              bitcast environmentPointerUntyped (ptr environmentType)

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

emitExpression :: (MonadState (Map Id Operand) m, MonadModuleBuilder m, MonadIRBuilder m, MonadFix m)
               => Maybe Operand
               -> EmitableExpr
               -> m Operand
emitExpression env =
    bipara (emitExpr env) (emitValue env)

emitExpr :: (MonadState (Map Id Operand) m, MonadIRBuilder m, MonadFix m)
         => Maybe Operand
         -> ExprF (Either GlobalMarker ClosureMarker) Type (EmitableExpr, m Operand) (EmitableValue, m Operand)
         -> m Operand
emitExpr environment (AppF _ ty (_, emitFunction) (_, emitArg)) =
    do
        closure <- emitFunction
        argument <- emitArg
        functionPtr <- extractValue closure [0]
        environmentPtr <- extractValue closure [1]
        call functionPtr [(environmentPtr, []), (argument, [])]

emitExpr environment (BinopF _ rTy op (lhs, emitLHS) (rhs, emitRHS)) =
    do
        lhsArgument <- emitLHS; rhsArgument <- emitRHS
        let operator = llvmOperator (annotation lhs) op (annotation rhs) rTy
        operator lhsArgument rhsArgument

emitExpr environment (LetDiamondF _ ty pat mty (now, emitNow) (next, emitNext)) =
    error "Let diamond not yet supported."

emitExpr environment (ValF _ ty (_, emitValue)) = emitValue

emitExpr environment (CaseF _ ty (swon, emitSwExpr) cases) =
    mdo
        resultStorage <- alloca (llvmType ty) Nothing 4
        switchOnExpr <- emitSwExpr

        br tryFirstPattern
        tryFirstPattern <- foldrM (flip (emitCaseArm switchOnExpr resultStorage successLabel)) failureLabel cases

        failureLabel <- block
        trap

        successLabel <- block
        load resultStorage 4

        {- A pattern match attempts to bind all vars in it + check conditions, before
           setting the result and jumping to the exit, if the pattern match fails then we want to jump
           to the next branch.

           emitCaseArm :: (MonadIRBuilder m) => Name -> (Pattern, m Operand) -> Name -> m Name
           emitCaseArm successLabel (pat, emitArm) failLabel =

                -- return the name of the generated block

           to generate the failure case before the success case we need to
           generate the cases in reverse order.

           This means we need to unconditionally jump to resulting label.

           tryFirstPattern <- foldrM (makeJump switchOnExpr successLabel) cases -}

emitCaseArm :: (MonadState (Map Id Operand) m, MonadFix m, MonadIRBuilder m)
            => Operand
            -> Operand
            -> Name
            -> Name
            -> (Pattern GrType, (EmitableExpr, m Operand))
            -> m Name
emitCaseArm switchOnExpr resultStorage successLabel failLabel =
    \case
        (PInt _ _ n, (_, emitArmExpr)) -> mdo
            checkMatches <- block
            matches <- icmp IP.EQ (IR.ConstantOperand $ intConstant n) switchOnExpr
            condBr matches storeResult failLabel

            storeResult <- block
            result <- emitArmExpr
            store resultStorage 4 result
            br successLabel
            return checkMatches
        (PVar _ ty ident, (_, emitArmExpr)) -> do
            thisCase <- block
            addLocal ident switchOnExpr
            result <- emitArmExpr
            store resultStorage 4 result
            br successLabel
            return thisCase
        (pat, _) ->
            error $ "Pattern not supported " ++ show pat

addLocal name operand =
    modify $ insertWith (\_ _ -> error "Unexpected name shadowing") name operand

clearLocals :: (MonadState (Map Id Operand) m)
    => m ()
clearLocals =
    modify (const Map.empty)

local :: (MonadState (Map Id Operand) m)
      => Id
      -> m Operand
local name =
    do
        sym <- gets $ Map.lookup name
        case sym of
            Just op -> return op
            Nothing -> error $ internalName name ++ " registered as a local, missing call to addLocal?\n" ++ show sym

llvmOperator :: (MonadIRBuilder m)
             => GrType
             -> String
             -> GrType
             -> GrType
             -> (Operand -> Operand -> m Operand)
llvmOperator (TyCon (MkId "Int")) "+" (TyCon (MkId "Int")) (TyCon (MkId "Int")) = add
llvmOperator (TyCon (MkId "Int")) "-" (TyCon (MkId "Int")) (TyCon (MkId "Int")) = sub
llvmOperator (TyCon (MkId "Int")) "*" (TyCon (MkId "Int")) (TyCon (MkId "Int")) = mul
llvmOperator (TyCon (MkId "Int")) "/" (TyCon (MkId "Int")) (TyCon (MkId "Int")) = sdiv
llvmOperator (TyCon (MkId "Int")) cmpOp (TyCon (MkId "Int")) (TyCon (MkId "Bool"))
    | cmpOp == "≡" = icmp IP.EQ
    | cmpOp == "≤" = icmp IP.SGE
    | cmpOp == "≥" = icmp IP.SLE
    | cmpOp == "<"  = icmp IP.SLT
    | cmpOp == ">"  = icmp IP.SGT
llvmOperator (TyCon (MkId "Float")) "+" (TyCon (MkId "Float")) (TyCon (MkId "Float")) = fadd
llvmOperator (TyCon (MkId "Float")) "-" (TyCon (MkId "Float")) (TyCon (MkId "Float")) = fsub
llvmOperator (TyCon (MkId "Float")) "*" (TyCon (MkId "Float")) (TyCon (MkId "Float")) = fmul
llvmOperator (TyCon (MkId "Float")) "/" (TyCon (MkId "Float")) (TyCon (MkId "Float")) = fdiv
llvmOperator (TyCon (MkId "Float")) cmpOp (TyCon (MkId "Float")) (TyCon (MkId "Bool"))
    | cmpOp == "≡" = fcmp FPP.UEQ
    | cmpOp == "≤" = fcmp FPP.UGE
    | cmpOp == "<"  = fcmp FPP.ULT
    | cmpOp == "≥" = fcmp FPP.ULE
    | cmpOp == ">"  = fcmp FPP.UGT

llvmOperator leftType operator rightType returnType =
    error $ "Undefined operator (" ++ operator ++ ") : " ++ lhs ++ " -> " ++ rhs ++ " -> " ++ ret
    where lhs = (show leftType)
          rhs = (show rightType)
          ret = (show returnType)

emitValue :: MonadFix m
          => MonadState (Map Id Operand) m
          => MonadModuleBuilder m
          => MonadIRBuilder m
          => Maybe Operand
          -> ValueF (Either GlobalMarker ClosureMarker) Type (EmitableValue, m Operand) (EmitableExpr, m Operand)
          -> m Operand
-- TODO make normalised definitions have strings as args, eliminate patterns from lambda args.
emitValue _ (PromoteF ty (_, emitEx)) = error "Let diamond not yet supported."
emitValue _ (PureF ty (_, emitEx)) = error "Let diamond not yet supported."
emitValue _ (VarF ty ident) = local ident
emitValue _ (NumIntF n) = IC.int32 (toInteger n)
emitValue _ (NumFloatF n) = IC.double n
emitValue _ (CharLiteralF ch) =
    return $ IR.ConstantOperand (charConstant ch)
emitValue _ (StringLiteralF str) =
    return $ IR.ConstantOperand (stringConstant $ unpack str)
emitValue _ (ExtF a (Left (GlobalVar ty ident))) = do
    let ref = IR.ConstantOperand $ C.GlobalReference (ptr (llvmType ty)) (definitionNameFromId ident)
    load ref 4
emitValue environment (ExtF ty (Right cm)) =
    emitClosureMarker environment cm
    where emitClosureMarker (Just env) (CapturedVar ty ident idx) =
              do
                  addr <- gep env $ (IR.ConstantOperand . intConstant) <$> [0, idx]
                  load addr 4
          emitClosureMarker Nothing (CapturedVar _ _ _) =
              error "Use of captured variable when no environment present."
          emitClosureMarker maybeParentEnv (MakeClosure ident initializer) =
              do
                  let (ClosureEnvironmentInit environmentTypeName variableInitializers) = initializer
                  let environmentType = NamedTypeReference (mkName environmentTypeName)
                  environmentVoidPtr <- mallocEnvironment environmentType
                  environmentTypedPtr <- bitcast environmentVoidPtr (ptr environmentType)
                  emitEnvironmentInit variableInitializers environmentTypedPtr maybeParentEnv
                  emitClosureConstruction ident ty environmentVoidPtr
          emitClosureMarker _ (MakeTrivialClosure identifier) =
              return $ IR.ConstantOperand $ makeTrivialClosure identifier ty
          emitClosureMarker :: (MonadIRBuilder m, MonadModuleBuilder m)
                            => Maybe Operand
                            -> ClosureMarker
                            -> m Operand
{- TODO: Support tagged unions, also affects Case.
Requires information from previously emited enum + variant types.
emitValue environment (ExtF ty (ADTMarker adt)) =
    emitADT adt
    data Constructor = Constructor {
        possibleVariants :: Integer
        varaint :: Integer
        values :: [Value]
    } This is silly, this needs to go in a dictionary.
    where emitADT (Constructor 1 1 []) =
            -- No Tag, Just Val room for further optimization.
          emitADT (Constructor 1 1 (v:vs))
            -- No Tag, Just Val
          emitADT (Constructor n variant []) | n > 1 =
            -- Only Tag, No data this case probably falls out automatically.
          emitADT (Constructor n variant (v:vs)) =
-}
emitValue _ (AbsF _ _ _ _) =
    error "Encountered Abs. It should have been removed by closure conversion."
emitValue _ (ConstrF _ _ _) =
    error "Encountered Constr. It should have been removed by constructor conversion."

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
                  uninitAddr <- gep env $ (IR.ConstantOperand . intConstant) <$> [0, n]
                  parentAddr <- gep parentEnv $ (IR.ConstantOperand . intConstant) <$> [0, idx]
                  value <- load parentAddr 4
                  store uninitAddr 4 value
          emitEnvironmentVariableInit n (FromLocalScope ident ty) =
              do
                  uninitAddr <- gep env $ (IR.ConstantOperand . intConstant) <$> [0, n]
                  let value = IR.LocalReference (llvmType ty) (localNameFromId ident)
                  store uninitAddr 4 value

emitClosureConstruction :: (MonadIRBuilder m)
                        => Id
                        -> GrType
                        -> Operand
                        -> m Operand
emitClosureConstruction ident ty environmentPtr =
    do
        let closureType  = llvmType ty
        let undefClosure = IR.ConstantOperand $ C.Undef closureType
        let functionPtr  = IR.ConstantOperand $ makePointerToFunction ident ty
        closure  <- insertValue undefClosure functionPtr [0]
        closure' <- insertValue closure environmentPtr   [1]
        return closure'

emitDataDecl = error "Cannot emit data decls yet!"

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

malloc :: Constant
malloc = C.GlobalReference functionType name
         where name = mkName "malloc"
               functionType = ptr (FunctionType (ptr i8) [i64] False)

mallocEnvironment :: (MonadIRBuilder m) => IrType -> m Operand
mallocEnvironment ty =
    call (IR.ConstantOperand malloc) [(IR.ConstantOperand $ sizeOf ty, [])]

abort :: Constant
abort = C.GlobalReference functionType name
        where name = mkName "abort"
              functionType = ptr (FunctionType void [] False)

trap :: (MonadIRBuilder m) => m ()
trap = (call (IR.ConstantOperand abort) []) >> return ()
