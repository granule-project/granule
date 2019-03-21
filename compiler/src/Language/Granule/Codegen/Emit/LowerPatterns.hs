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
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST as IR


emitCaseArm :: (MonadState EmitterState m, MonadFix m, MonadIRBuilder m)
            => Operand
            -> Operand
            -> Name
            -> Name
            -> (Pattern GrType, (EmitableExpr, m Operand))
            -> m Name
emitCaseArm switchOnExpr resultStorage successLabel failLabel =
    emitArm
    where emitArm (PInt _ _ n, (_, emitArmExpr)) =
              mdo
                  checkMatches <- block
                  matches <- icmp IP.EQ (IR.ConstantOperand $ intConstant n) switchOnExpr
                  condBr matches storeResult failLabel

                  storeResult <- block
                  result <- emitArmExpr
                  store resultStorage 4 result
                  br successLabel
                  return checkMatches
          emitArm (PVar _ ty ident, (_, emitArmExpr)) =
              do
                  thisCase <- block
                  addLocal ident switchOnExpr
                  result <- emitArmExpr
                  store resultStorage 4 result
                  br successLabel
                  return thisCase
          emitArm (pat, _) =
              error $ "Pattern not supported " ++ show pat
