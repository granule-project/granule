{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.Granule.Codegen.Emit.LowerExpression where

import Language.Granule.Codegen.ClosureFreeDef (ClosureMarker)
import Language.Granule.Codegen.MarkGlobals (GlobalMarker, GlobalMarker(..))
import Language.Granule.Codegen.Emit.LowerOperator
import Language.Granule.Codegen.Emit.LowerType (llvmType)
import Language.Granule.Codegen.Emit.EmitableDef
import Language.Granule.Codegen.Emit.LowerPatterns (emitCaseArm)
import Language.Granule.Codegen.Emit.LowerClosure (emitClosureMarker)
import Language.Granule.Codegen.Emit.EmitterState
import Language.Granule.Codegen.Emit.Names
import Language.Granule.Codegen.Emit.Primitives (trap)
import Language.Granule.Codegen.Emit.LLVMHelpers (stringConstant, charConstant)

import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Annotated (annotation)
import Language.Granule.Syntax.Type as GRType

import Control.Monad.State.Strict hiding (void)
import Control.Monad.Fix (MonadFix)
import Data.Foldable (foldrM)
import Data.Bifunctor.Foldable
import Data.Text (unpack)

import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction

import LLVM.AST (Operand)
import LLVM.AST.Type (ptr)
import LLVM.AST.Constant as C
import qualified LLVM.IRBuilder.Constant as IC
import qualified LLVM.AST as IR
import qualified LLVM.AST.Type as IRType

type GrType = GRType.Type
type IrType = IRType.Type

emitExpression :: (MonadState EmitterState m, MonadModuleBuilder m, MonadIRBuilder m, MonadFix m)
               => Maybe Operand
               -> EmitableExpr
               -> m Operand
emitExpression env =
    bipara (emitExpr env) (emitValue env)

emitExpr :: (MonadState EmitterState m, MonadIRBuilder m, MonadFix m)
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
        let emitArm = emitCaseArm switchOnExpr resultStorage successLabel -- :: (Pattern GrType, (EmitableExpr, m Operand)) -> IR.Name -> IR.Name
        tryFirstPattern <- foldrM emitArm failureLabel cases

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

-- The following case should now really be possible because holes stop the type checker.
emitExpr environment (HoleF _ _) = error "Trying to compile a hole"

emitValue :: MonadFix m
          => MonadState EmitterState m
          => MonadModuleBuilder m
          => MonadIRBuilder m
          => Maybe Operand
          -> ValueF (Either GlobalMarker ClosureMarker) GrType (EmitableValue, m Operand) (EmitableExpr, m Operand)
          -> m Operand
-- TODO make normalised definitions have strings as args, eliminate patterns from lambda args.
emitValue _ (PromoteF ty (_, emitEx)) = emitEx
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
    emitClosureMarker ty environment cm
{- TODO: Support tagged unions, also affects Case.
Requires information from previously emited enum + variant types.
emitValue environment (ExtF ty (ADTMarker adt)) =
    emitADT adt
    data Constructor = Constructor {
        possibleVariants :: Integer
        varaint :: Integer
        values :: [Value]
    } Some of this info should be added to emitter state.
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
{-    do
emitValue _ (ConstrF ty (MkId "(,)") []) =
    environmentVoidPtr <- mallocEnvironment environmentType
    environmentTypedPtr <- bitcast environmentVoidPtr (ptr environmentType)
    emitEnvironmentInit variableInitializers environmentTypedPtr maybeParentEnv
    emitClosureConstruction ident ty environmentVoidPtr -}

emitValue _ (ConstrF _ _ _) =
    error "Encountered Constr. It should have been removed by constructor conversion."
