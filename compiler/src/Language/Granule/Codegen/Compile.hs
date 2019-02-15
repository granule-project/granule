{-# LANGUAGE ImplicitParams #-}
module Language.Granule.Codegen.Compile where

import Control.Exception (SomeException)
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Type
import Language.Granule.Codegen.NormalisedDef
import Language.Granule.Codegen.TopsortDefinitions
import Language.Granule.Codegen.ConvertClosures
import Language.Granule.Codegen.EmitLLVM
import Language.Granule.Codegen.MarkGlobals
import Language.Granule.Utils
import qualified LLVM.AST as IR
--import Language.Granule.Syntax.Pretty
import Debug.Trace

compile :: String -> AST () Type -> Either SomeException IR.Module
compile moduleName typedAST =
    let ?globals       = defaultGlobals in
    let normalised     = trace (show typedAST) (normaliseDefinitions typedAST)
        markedGlobals  = markGlobals normalised
        (Ok topsorted) = topologicallySortDefinitions markedGlobals
        closureFree    = convertClosures topsorted
    in emitLLVM moduleName closureFree
    -- NOTE Closures have the wrong type
