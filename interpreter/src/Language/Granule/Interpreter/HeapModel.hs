module Language.Granule.Interpreter.HeapModel where

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Context
--import Language.Granule.Utils

heapEval :: AST () () -> IO (Maybe (Value () ()))
heapEval _ = return Nothing

heapEvalDefs :: [Def () ()] -> IO (Ctxt (Value () ()))
heapEvalDefs defs = return []