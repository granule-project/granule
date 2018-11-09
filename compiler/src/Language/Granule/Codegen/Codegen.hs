{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
module Language.Granule.Codegen.Codegen where

import Control.Exception (SomeException)

import Language.Granule.Syntax.Def

import qualified LLVM.AST.Float as F
import qualified LLVM.AST.Constant as C
--import qualified LLVM.AST.IntegerPredicate as P
import qualified LLVM.AST.Type as IRType
import qualified LLVM.AST as IR

import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction

codegen :: AST () () -> Either SomeException IR.Module
codegen ast = Right $ buildModule "granule" $ mdo
 function "main" [] IRType.double $ \[] -> mdo
   _entry <- block `named` "entry"
   r <- fadd (IR.ConstantOperand (C.Float (F.Double 10))) (IR.ConstantOperand (C.Float (F.Double 20)))
   ret r
