{-# LANGUAGE RecordWildCards #-}

module Language.Granule.Synthesis.RewriteHoles where

import Control.Arrow (second)
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
  let source = Text.pack input
  debugM' "AST" (show ast)
  let refactored = refactorEmptyHoles source ast
  putStrLn (Text.unpack refactored)
  return ()
rewriteHole _ _ _ = error "Impossible"

refactorEmptyHoles :: (?globals :: Globals) => Source -> AST () () -> Source
refactorEmptyHoles source =
  runIdentity . (\ast -> reprint astReprinter ast source) . emptyHoles

astReprinter :: (?globals :: Globals) => Reprinting Identity
astReprinter = catchAll `extQ` reprintExpr
  where
    reprintExpr x = genReprinting (return . Text.pack . pretty) (x :: Def () ())

-- Converts e.g. {! x !} to ?
-- TODO: Support nested holes
-- TODO: Holes inside Val e.g. lambda
emptyHoles :: AST () () -> AST () ()
emptyHoles ast =
  (ast {definitions = map emptyHolesDef (definitions ast) })

emptyHolesDef :: Def () () -> Def () ()
emptyHolesDef def =
  def
  { defEquations = map emptyHolesEqn (defEquations def)
  , defRefactored = True }

emptyHolesEqn :: Equation () () -> Equation () ()
emptyHolesEqn eqn =
  eqn
  { equationBody = emptyHolesExpr (equationBody eqn)
  , equationRefactored = True }

emptyHolesExpr :: Expr () () -> Expr () ()
emptyHolesExpr (Hole sp a _ _) = Hole sp a True []
emptyHolesExpr (App sp a rf e1 e2) = App sp a rf (emptyHolesExpr e1) (emptyHolesExpr e2)
emptyHolesExpr (Binop sp a rf op e1 e2) = Binop sp a rf op (emptyHolesExpr e1) (emptyHolesExpr e2)
emptyHolesExpr (LetDiamond sp a rf pat ty e1 e2) = LetDiamond sp a rf pat ty (emptyHolesExpr e1) (emptyHolesExpr e2)
emptyHolesExpr (Case sp a rf e cases) = Case sp a rf (emptyHolesExpr e) (map (second emptyHolesExpr) cases)
emptyHolesExpr v@Val{} = v