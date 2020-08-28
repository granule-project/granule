{-# LANGUAGE ScopedTypeVariables #-}

module Language.Granule.Synthesis.RewriteHoles
  ( rewriteHoles
  ) where

import Control.Arrow (second)
import Control.Monad (void)
import Data.Maybe (fromJust)
import qualified Data.Text.Lazy as Text
import Text.Reprinter hiding (Span)

import Language.Granule.Context

import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span (Span, encompasses)
import Language.Granule.Synthesis.Refactor (refactorEqn)

import Language.Granule.Utils

-- Rewrites holes in the file by splitting on their potential cases.
rewriteHoles ::
     (?globals :: Globals)
  => String
  -> AST () ()
  -> Bool
  -> [(Span, Ctxt (Pattern ()), Expr () Type)]
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
     (?globals :: Globals) => Source -> [(Span, Ctxt (Pattern ()), Expr () Type)] -> AST () () -> Source
holeRewriter source cases =
  runIdentity . (\ast -> reprint astReprinter ast source) . holeRefactor cases

-- The reprinter which runs on a refactored AST. Reprinting is done at the Def
-- level down, as the equations across a definition are subject to change.
astReprinter :: (?globals :: Globals) => Reprinting Identity
astReprinter = catchAll `extQ` reprintEqnList `extQ` reprintEqn
  where
    reprintEqn eqn =
      genReprinting (return . Text.pack . pretty) (eqn :: Equation () ())

    reprintEqnList eqn =
      genReprinting (return . Text.pack . pretty) (eqn :: EquationList () ())

-- Refactor an AST by refactoring its definitions.
holeRefactor :: [(Span, Ctxt (Pattern ()), Expr () Type)] -> AST () () -> AST () ()
holeRefactor cases ast =
  ast {definitions = map (holeRefactorDef cases) (definitions ast)}

-- Refactor a definition by refactoring its list of equations.
holeRefactorDef :: [(Span, Ctxt (Pattern ()), Expr () Type)] -> Def () () -> Def () ()
holeRefactorDef cases def =
  def {defEquations = holeRefactorEqnList cases (defEquations def)}

-- Refactors a list of equations by updating each with the relevant patterns.
holeRefactorEqnList ::
     [(Span, Ctxt (Pattern ()), Expr () Type)] -> EquationList () () -> EquationList () ()
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
             (map (\(_, cs, t) ->
             -- Fill in the hole
               let eqn' = holeRefactorEqn eqn t
                   oldPatterns = equationPatterns eqn'
               in
                 if null cs && not (null oldPatterns)
                   then eqn'
                   else refactorEqn (eqn' {equationPatterns = map (\oldPat -> foldr (flip (uncurry . refactorPattern)) oldPat cs) oldPatterns})) relCases, True)

-- Refactors an equation by refactoring the expression in its body.
holeRefactorEqn ::  Equation () () -> Expr () Type -> Equation () ()
holeRefactorEqn eqn goal =
  eqn { equationRefactored = True
      , equationBody = holeRefactorExpr goal (equationBody eqn) }

-- Refactors an expression by filling the hole with the new goal (could be another hole)
holeRefactorExpr :: Expr () Type -> Expr () () -> Expr () ()
holeRefactorExpr goal (Hole sp a _ _) = void goal
holeRefactorExpr goal (App sp a rf e1 e2) =
  App sp a rf (holeRefactorExpr goal e1) (holeRefactorExpr goal e2)
holeRefactorExpr goal (AppTy sp a rf e t) =
  AppTy sp a rf (holeRefactorExpr goal e) t
holeRefactorExpr goal (Binop sp a rf op e1 e2) =
  Binop sp a rf op (holeRefactorExpr goal e1) (holeRefactorExpr goal e2)
holeRefactorExpr goal (LetDiamond sp a rf pat ty e1 e2) =
  LetDiamond sp a rf pat ty (holeRefactorExpr goal e1) (holeRefactorExpr goal e2)
holeRefactorExpr goal (Case sp a rf e cases) =
  Case sp a rf (holeRefactorExpr goal e) (map (second (holeRefactorExpr goal)) cases)
holeRefactorExpr goal (TryCatch sp a rf e1 pat ty e2 e3) =
  TryCatch sp a rf (holeRefactorExpr goal e1) pat ty (holeRefactorExpr goal e2) (holeRefactorExpr goal e3)
-- TODO: for maximum expressivity with holes we should recursively refacor inside values as well (as they contain exprs)
holeRefactorExpr goal (Val sp a rf v) = Val sp a rf (holeRefactorVal goal v)

holeRefactorVal :: Expr () Type -> Value () () -> Value () ()
holeRefactorVal goal (Abs a p mt expr) = Abs a p mt (holeRefactorExpr goal expr)
holeRefactorVal goal (Promote a expr)  = Promote a (holeRefactorExpr goal expr)
holeRefactorVal goal (Pure a expr)     = Pure a (holeRefactorExpr goal expr)
holeRefactorVal goal (Constr a v vals) = Constr a v (map (holeRefactorVal goal) vals)
holeRefactorVal goal v = v

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
refactorPattern (PConstr sp () _ id ps) id' subpat =
  let ps' = map (\p -> refactorPattern p id' subpat) ps
  in PConstr sp () (any patRefactored ps') id ps'


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

-- Finds associated cases for a given equation, based on spans.
findRelevantCase :: Equation () () -> [(Span, Ctxt (Pattern ()), Expr () Type)] -> [(Span, Ctxt (Pattern ()), Expr () Type)]

findRelevantCase eqn =
  filter (\(span, case', expr) -> equationSpan eqn `encompasses` span)
