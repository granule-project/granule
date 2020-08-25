{-# LANGUAGE ScopedTypeVariables #-}

module Language.Granule.Synthesis.RewriteHoles
  ( rewriteHoles
  ) where

import Control.Arrow (second)
import Control.Monad (void)
import Data.Maybe (fromJust, listToMaybe)
import qualified Data.Text.Lazy as Text
import Text.Reprinter

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span (encompasses)

import Language.Granule.Utils

-- Rewrites holes in the file by splitting on their potential cases.
rewriteHoles ::
     (?globals :: Globals)
  => String
  -> AST () ()
  -> Bool
  -> [[(Id, Pattern ())]]
  -> IO ()
rewriteHoles _ _ _ [] = return ()
rewriteHoles input ast keepBackup cases = do
  let source = Text.pack input
  let refactored = holeRewriter source cases ast
  let file = fromJust $ globalsSourceFilePath ?globals
  void $ writeSrcFile file keepBackup (Text.unpack refactored)

-- The top level rewriting function, transforms a given source file and
-- corresponding AST.
holeRewriter ::
     (?globals :: Globals)
  => Source
  -> [[(Id, Pattern ())]]
  -> AST () ()
  -> Source
holeRewriter source cases =
  runIdentity . (\ast -> reprint astReprinter ast source) . holeRefactor cases

-- The reprinter which runs on a refactored AST. Reprinting is done at the Def
-- level down, as the equations across a definition are subject to change.
astReprinter :: (?globals :: Globals) => Reprinting Identity
astReprinter = catchAll `extQ` reprintEqnList
  where
    reprintEqnList eqns =
      genReprinting (return . Text.pack . pretty) (eqns :: EquationList () ())

-- Refactor an AST by refactoring its definitions.
holeRefactor :: [[(Id, Pattern ())]] -> AST () () -> AST () ()
holeRefactor cases ast =
  ast {definitions = map (holeRefactorDef cases) (definitions ast)}

-- Refactor a definition by refactoring its list of equations.
holeRefactorDef :: [[(Id, Pattern ())]] -> Def () () -> Def () ()
holeRefactorDef cases def =
  def {defEquations = holeRefactorEqnList cases (defEquations def)}

-- Refactors a list of equations by updating each with the relevant patterns.
holeRefactorEqnList ::
     [[(Id, Pattern ())]] -> EquationList () () -> EquationList () ()
holeRefactorEqnList cases eqns =
  eqns {equations = newEquations, equationsRefactored = refactored}
  where
    allUpdated = map updateEqn (equations eqns)
    newEquations = concatMap fst allUpdated
    refactored = any snd allUpdated
    -- Updates an individual equation with the relevant cases, returning a tuple
    -- containing the new equation(s) and whether a refactoring was performed.
    updateEqn :: Equation () () -> ([Equation () ()], Bool)
    updateEqn eqn =
      let relCases = findRelevantCase eqn cases
      in case relCases of
           [] -> ([eqn], False)
           _ ->
             let eqn' = holeRefactorEqn eqn
                 oldPatterns = equationPatterns eqn'
                 updateOldPatterns cs =
                   eqn'
                   { equationPatterns =
                       map
                         (\oldPat ->
                            foldr (flip (uncurry . refactorPattern)) oldPat cs)
                         oldPatterns
                   }
             in (map updateOldPatterns relCases, True)

-- Refactors a pattern by traversing to the rewritten variable and replacing
-- the variable with the subpattern.
refactorPattern :: Pattern () -> Id -> Pattern () -> Pattern ()
refactorPattern p@(PVar _ _ _ id) id' subpat
  | id == id' = subpat
  | otherwise = p
refactorPattern p@PWild {} _ _ = p
refactorPattern (PBox sp () _ p) id' subpat =
  let p' = refactorPattern p id' subpat
  in PBox sp () (patRefactored p') p'
refactorPattern p@PInt {} _ _ = p
refactorPattern p@PFloat {} _ _ = p
refactorPattern (PConstr sp () _ conId ps) id subpat =
  let ps' = map (\p -> refactorPattern p id subpat) ps
  in PConstr sp () (any patRefactored ps') conId ps'

-- Refactors an equation by refactoring the expression in its body.
holeRefactorEqn :: Equation () () -> Equation () ()
holeRefactorEqn eqn = eqn {equationBody = holeRefactorExpr (equationBody eqn)}

-- Refactors an expression by 'emptying' all holes, i.e. removing the variables
-- contained in it. This is done recursively.
holeRefactorExpr :: Expr () () -> Expr () ()
holeRefactorExpr (Hole sp a _ []) = Hole sp a False []
holeRefactorExpr (Hole sp a _ _) = Hole sp a True []
holeRefactorExpr (App sp a rf e1 e2) =
  App sp a rf (holeRefactorExpr e1) (holeRefactorExpr e2)
holeRefactorExpr (Binop sp a rf op e1 e2) =
  Binop sp a rf op (holeRefactorExpr e1) (holeRefactorExpr e2)
holeRefactorExpr (LetDiamond sp a rf pat ty e1 e2) =
  LetDiamond sp a rf pat ty (holeRefactorExpr e1) (holeRefactorExpr e2)
holeRefactorExpr (TryCatch sp a rf e1 pat ty e2 e3) =
  TryCatch sp a rf (holeRefactorExpr e1) pat ty (holeRefactorExpr e2) (holeRefactorExpr e3)
holeRefactorExpr (Handled sp a rf e t oprs) =
  Handled sp a rf (holeRefactorExpr e) t (map (second holeRefactorExpr) oprs)
holeRefactorExpr (Case sp a rf e cases) =
  Case sp a rf (holeRefactorExpr e) (map (second holeRefactorExpr) cases)
-- TODO: for maximum expressivity with holes we should recursively refactor inside values as well (as they contain exprs)
holeRefactorExpr v@Val {} = v

-- Finds potentially relevant cases for a given equation, based on spans.
findRelevantCase ::
     Equation () () -> [[(Id, Pattern ())]] -> [[(Id, Pattern ())]]
findRelevantCase eqn =
  filter
    (\case' ->
       case listToMaybe case' of
         Nothing -> False
         Just h -> equationSpan eqn `encompasses` getFirstParameter (snd h))
