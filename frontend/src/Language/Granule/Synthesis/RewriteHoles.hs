{-# LANGUAGE RecordWildCards #-}

module Language.Granule.Synthesis.RewriteHoles where

--import Debug.Trace
import qualified Data.Text.Lazy as Text
import Text.Reprinter

import Language.Granule.Checker.Monad

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pretty

import Language.Granule.Utils

{-
  = HoleMessage
    { errLoc :: Span , holeTy :: Type, context :: Ctxt Assumption, tyContext :: Ctxt (Kind, Quantifier), cases :: ([Id], [[Pattern ()]])}
-}
rewriteHole :: (?globals :: Globals) => String -> AST () () -> CheckerError -> IO ()
rewriteHole input ast HoleMessage {..} = do
  debugM' "ast" (show ast)
  let source = Text.pack input
  debugM' "src" (Text.unpack source)
  let refactored = refactorEmptyHoles source ast
  debugM' "rft" (Text.unpack refactored)
  return ()
rewriteHole _ _ _ = error "Impossible"

refactorEmptyHoles :: (?globals :: Globals) => Source -> AST () () -> Source
refactorEmptyHoles source =
  runIdentity . (\ast -> reprint astReprinter ast source) . emptyHoles

astReprinter :: (?globals :: Globals) => Reprinting Identity
astReprinter = catchAll `extQ` reprintExpr
  where
    reprintExpr x = genReprinting (return . Text.pack . pretty) (x :: Expr () ())

-- Converts e.g. {! x !} to ?
-- TODO: Also pass back count of rewritten holes
-- TODO: Support nested holes
emptyHoles :: AST v e -> AST v e
emptyHoles ast =
  ast {definitions = map emptyHolesDef (definitions ast) }

emptyHolesDef :: Def v e -> Def v e
emptyHolesDef def =
  def
  {defEquations = map emptyHolesEqn (defEquations def) }

emptyHolesEqn :: Equation v e -> Equation v e
emptyHolesEqn eqn =
  eqn
  { equationBody = emptyHolesExpr (equationBody eqn) }

emptyHolesExpr :: Expr v e -> Expr v e
emptyHolesExpr (Hole sp a _ _) = Hole sp a True []
emptyHolesExpr e = e