{-# LANGUAGE ScopedTypeVariables #-}

module Language.Granule.Synthesis.RewriteHoles where

import Control.Arrow (second)
import Control.Monad (void)
import Data.Maybe (fromJust)
import qualified Data.Text.Lazy as Text
import Text.Reprinter

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty

import Language.Granule.Utils

-- Rewrites holes in the file by splitting on their potential cases.
rewriteHole ::
     (?globals :: Globals)
  => String
  -> AST () ()
  -> Bool
  -> ([Id], [[Pattern ()]])
  -> IO ()
rewriteHole input ast keepBackup cases = do
  let source = Text.pack input
  let refactored = rewriteHoles source (snd cases) ast
  let file = fromJust $ globalsSourceFilePath ?globals
  void $ writeSrcFile file keepBackup (Text.unpack refactored)

-- TODO: Support nested holes
-- TODO: Holes inside Val e.g. lambda
-- TODO: Support multiple equations before refactor
rewriteHoles ::
     (?globals :: Globals) => Source -> [[Pattern ()]] -> AST () () -> Source
rewriteHoles source cases =
  runIdentity . (\ast -> reprint astReprinter ast source) . holeRefactor cases

-- The reprinter which runs on a refactored AST. Reprinting is done at the Def
-- level down, as the equations across a definition are subject to change.
astReprinter :: (?globals :: Globals) => Reprinting Identity
astReprinter = catchAll `extQ` reprintDef
  where
    reprintDef x = genReprinting (return . Text.pack . pretty) (x :: Def () ())

-- Refactor an AST by refactoring its definitions.
holeRefactor :: [[Pattern ()]] -> AST () () -> AST () ()
holeRefactor cases ast =
  ast {definitions = map (holeRefactorDef cases) (definitions ast)}

-- Refactors a definition by updating its list of equations.
holeRefactorDef :: [[Pattern ()]] -> Def () () -> Def () ()
holeRefactorDef cases def =
  def {defEquations = updateEquations (defEquations def), defRefactored = True}
  where
    updateEquations [eqn] =
      let updated = holeRefactorEqn eqn
      in map
           (\cas -> (\pats eqn -> eqn {equationPatterns = pats}) cas updated)
           cases
    updateEquations _ = error "Only one LHS for now"

-- Refactors an equation by refactoring the expression in its body.
holeRefactorEqn :: Equation () () -> Equation () ()
holeRefactorEqn eqn = eqn {equationBody = holeRefactorExpr (equationBody eqn)}

-- Refactors an expression by 'emptying' all holes, i.e. removing the variables
-- contained in it. This is done recursively.
holeRefactorExpr :: Expr () () -> Expr () ()
holeRefactorExpr (Hole sp a _ _) = Hole sp a True []
holeRefactorExpr (App sp a rf e1 e2) =
  App sp a rf (holeRefactorExpr e1) (holeRefactorExpr e2)
holeRefactorExpr (Binop sp a rf op e1 e2) =
  Binop sp a rf op (holeRefactorExpr e1) (holeRefactorExpr e2)
holeRefactorExpr (LetDiamond sp a rf pat ty e1 e2) =
  LetDiamond sp a rf pat ty (holeRefactorExpr e1) (holeRefactorExpr e2)
holeRefactorExpr (Case sp a rf e cases) =
  Case sp a rf (holeRefactorExpr e) (map (second holeRefactorExpr) cases)
holeRefactorExpr v@Val {} = v
