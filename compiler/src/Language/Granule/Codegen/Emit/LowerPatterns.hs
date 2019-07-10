{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.Granule.Codegen.Emit.LowerPatterns where

import Control.Monad.Fix (MonadFix)
import Control.Monad.State.Strict hiding (void)

import Language.Granule.Syntax.Pattern
import Language.Granule.Codegen.Emit.EmitterState
import Language.Granule.Codegen.Emit.EmitableDef
import Language.Granule.Codegen.Emit.LLVMHelpers
import Language.Granule.Codegen.Emit.Types

import LLVM.AST (Operand, Name)
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction
import qualified LLVM.IRBuilder.Constant as IC
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.FloatingPointPredicate as FPP
import qualified LLVM.AST as IR

emitPattern :: (MonadState EmitterState m, MonadFix m, MonadIRBuilder m)
            => Name
            -> Name
            -> Operand
            -> Pattern GrType
            -> m ()
emitPattern successLabel failLabel matchOperand (PInt _ _ n) =
    do
        matches <- icmp IP.EQ (IR.ConstantOperand $ intConstant n) matchOperand
        condBr matches successLabel failLabel
emitPattern successLabel failLabel matchOperand (PFloat _ _ n) =
    do
        v <- IC.double n
        matches <- fcmp FPP.UEQ v matchOperand
        condBr matches successLabel failLabel

emitPattern successLabel failLabel matchOperand (PVar _ _ ident) =
    do
        addLocal ident matchOperand
        br successLabel

emitPattern successLabel failLabel matchOperand (PBox _ ty pattern) =
    emitPattern successLabel failLabel matchOperand pattern

emitPattern _ pattern _ _ = error $ "Unsupported pattern: " ++ (show pattern)

emitCaseArm :: (MonadState EmitterState m, MonadFix m, MonadIRBuilder m)
            => Operand
            -> Operand
            -> Name
            -> (Pattern GrType, (EmitableExpr, m Operand))
            -> Name
            -> m Name
emitCaseArm switchOnExpr resultStorage successLabel (pat, (_, emitArmExpr)) failLabel =
    mdo
        caseEntry <- block
        emitPattern storeResultLabel failLabel switchOnExpr pat

        storeResultLabel <- block
        result <- emitArmExpr
        store resultStorage 4 result
        br successLabel
        return caseEntry
