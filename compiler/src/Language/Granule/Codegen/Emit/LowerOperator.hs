module Language.Granule.Codegen.Emit.LowerOperator where
import Language.Granule.Codegen.Emit.MkId
import Language.Granule.Codegen.Emit.Types
import Language.Granule.Syntax.Type

import LLVM.AST (Operand)
import LLVM.IRBuilder.Instruction
import LLVM.IRBuilder.Monad
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.FloatingPointPredicate as FPP

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
    | cmpOp == "≤" = icmp IP.SLE
    | cmpOp == "<"  = icmp IP.SLT
    | cmpOp == "≥" = icmp IP.SGE
    | cmpOp == ">"  = icmp IP.SGT
llvmOperator (TyCon (MkId "Float")) "+" (TyCon (MkId "Float")) (TyCon (MkId "Float")) = fadd
llvmOperator (TyCon (MkId "Float")) "-" (TyCon (MkId "Float")) (TyCon (MkId "Float")) = fsub
llvmOperator (TyCon (MkId "Float")) "*" (TyCon (MkId "Float")) (TyCon (MkId "Float")) = fmul
llvmOperator (TyCon (MkId "Float")) "/" (TyCon (MkId "Float")) (TyCon (MkId "Float")) = fdiv
llvmOperator (TyCon (MkId "Float")) cmpOp (TyCon (MkId "Float")) (TyCon (MkId "Bool"))
    | cmpOp == "≡" = fcmp FPP.UEQ
    | cmpOp == "≤" = fcmp FPP.ULE
    | cmpOp == "<"  = fcmp FPP.ULT
    | cmpOp == "≥" = fcmp FPP.UGE
    | cmpOp == ">"  = fcmp FPP.UGT

llvmOperator leftType operator rightType returnType =
    error $ "Undefined operator (" ++ operator ++ ") : " ++ lhs ++ " -> " ++ rhs ++ " -> " ++ ret
    where lhs = (show leftType)
          rhs = (show rightType)
          ret = (show returnType)
