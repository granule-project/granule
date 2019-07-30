{-# LANGUAGE ImplicitParams #-}
module Language.Granule.Codegen.Compile where

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Type
import Language.Granule.Codegen.NormalisedDef
import Language.Granule.Codegen.TopsortDefinitions
import Language.Granule.Codegen.ConvertClosures
import Language.Granule.Codegen.Emit.EmitLLVM
import Language.Granule.Codegen.MarkGlobals
import qualified LLVM.AST as IR
--import Language.Granule.Syntax.Pretty
--import Debug.Trace

compile :: String -> AST () Type -> Either String IR.Module
compile moduleName typedAST =
  let normalised     = {-trace (show typedAST)-} (normaliseDefinitions typedAST)
      markedGlobals  = markGlobals normalised
      (Ok topsorted) = topologicallySortDefinitions markedGlobals
      closureFree    = convertClosures topsorted
  in emitLLVM moduleName closureFree
