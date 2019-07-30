module Language.Granule.Codegen.Emit.Primitives where
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction

import LLVM.AST (mkName, Operand(..))
import LLVM.AST.Constant (Constant, Constant(..))
import LLVM.AST.Type (i8, i32, i64, ptr, void, Type(..))

malloc :: Constant
malloc = GlobalReference functionType name
         where name = mkName "malloc"
               functionType = ptr (FunctionType (ptr i8) [i64] False)


abort :: Constant
abort = GlobalReference functionType name
        where name = mkName "abort"
              functionType = ptr (FunctionType void [] False)

trap :: (MonadIRBuilder m) => m ()
trap = (call (ConstantOperand abort) []) >> unreachable >> return ()

writeInt :: Constant
writeInt = GlobalReference functionType name
           where name = mkName "writeInt"
                 functionType = ptr (FunctionType void [i32] False)
