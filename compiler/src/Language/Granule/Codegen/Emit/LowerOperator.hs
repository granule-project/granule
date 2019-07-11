module Language.Granule.Codegen.Emit.LowerOperator where
import Language.Granule.Codegen.Emit.MkId
import Language.Granule.Codegen.Emit.Types
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Expr (Operator(..))

import LLVM.AST (Operand)
import LLVM.IRBuilder.Instruction
import LLVM.IRBuilder.Monad
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.FloatingPointPredicate as FPP

llvmOperator :: (MonadIRBuilder m)
             => GrType
             -> Operator
             -> GrType
             -> GrType
             -> (Operand -> Operand -> m Operand)
llvmOperator (TyCon (MkId "Int")) OpPlus (TyCon (MkId "Int")) (TyCon (MkId "Int")) = add
llvmOperator (TyCon (MkId "Int")) OpMinus (TyCon (MkId "Int")) (TyCon (MkId "Int")) = sub
llvmOperator (TyCon (MkId "Int")) OpTimes (TyCon (MkId "Int")) (TyCon (MkId "Int")) = mul
llvmOperator (TyCon (MkId "Int")) cmpOp (TyCon (MkId "Int")) (TyCon (MkId "Bool"))
    | cmpOp == OpEq = icmp IP.EQ
    | cmpOp == OpLesserEq = icmp IP.SLE
    | cmpOp == OpLesser  = icmp IP.SLT
    | cmpOp == OpGreaterEq = icmp IP.SGE
    | cmpOp == OpGreater  = icmp IP.SGT
llvmOperator (TyCon (MkId "Float")) OpPlus (TyCon (MkId "Float")) (TyCon (MkId "Float")) = fadd
llvmOperator (TyCon (MkId "Float")) OpMinus (TyCon (MkId "Float")) (TyCon (MkId "Float")) = fsub
llvmOperator (TyCon (MkId "Float")) OpTimes (TyCon (MkId "Float")) (TyCon (MkId "Float")) = fmul
llvmOperator (TyCon (MkId "Float")) cmpOp (TyCon (MkId "Float")) (TyCon (MkId "Bool"))
    | cmpOp == OpEq = fcmp FPP.UEQ
    | cmpOp == OpLesserEq = fcmp FPP.ULE
    | cmpOp == OpLesser  = fcmp FPP.ULT
    | cmpOp == OpGreaterEq = fcmp FPP.UGE
    | cmpOp == OpGreater  = fcmp FPP.UGT
llvmOperator leftType operator rightType returnType =
    error $ "Undefined operator (" ++ show operator ++ ") : " ++ lhs ++ " -> " ++ rhs ++ " -> " ++ ret
    where lhs = show leftType
          rhs = show rightType
          ret = show returnType
