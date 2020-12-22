{-# LANGUAGE DataKinds #-}
module Language.Granule.Synthesis.Refactor where

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers

-- Refactors a definition which contains abstractions in its equations
-- by pushing these abstractions into equation patterns
refactorDef :: Def () Type -> Def () Type
refactorDef (Def sp id ref (EquationList sp' id' ref' eqns) tyS) =
  Def sp id ref (EquationList sp' id' ref' (map refactorEqn eqns)) tyS

refactorEqn :: Equation v a -> Equation v a
refactorEqn (Equation sp name ref annotation pats body) =
  Equation sp name ref annotation newPats newBody
    where
      (newPats, newBody) = bubbleUpPatterns body pats

replaceInPats :: [Pattern a] -> Id -> Pattern a -> [Pattern a]
replaceInPats pats var pat' = map (\pat -> refactorPattern pat var pat') pats

-- Collect patterns and rewrite beta-redexes into richer patterns
bubbleUpPatterns :: Expr v a -> [Pattern a] -> ([Pattern a], Expr v a)
-- Top-level lambda => add the pattern `p` to the list of patterns and recurse
bubbleUpPatterns (Val _ _ _ (Abs _ p _ e)) pats =
  bubbleUpPatterns e (pats ++ [p])
-- Beta-redex whose argument is a variable
bubbleUpPatterns (App _ _ _ (Val _ _ _ (Abs _ p _ e)) (Val _ _ _ (Var _ x))) pats =
  bubbleUpPatterns e (replaceInPats pats x p)
bubbleUpPatterns e pats = (pats, e)

refactorCase :: Eq a => [Pattern a] -> Expr v a -> [([Pattern a], Expr v a)]
refactorCase pats (Case _ _ _ (Val _ _ _ (Var _ name)) casePats) =
  concatMap (\(pat, body) -> refactorCase (replaceInPats pats name pat) body) casePats

-- Refactors a case expression to pattern match on the ADT at the function equation level
refactorCaseEqn :: Eq a => Equation v a -> [Equation v a]
refactorCaseEqn (Equation sp name ref ant pats body) =
  let refactors = refactorCase pats body in
  map (\(x,y) -> Equation sp name ref ant x y) refactors

-- Refactors a pattern by traversing to the rewritten variable and replacing
-- -- the variable with the subpattern.

-- refactorPattern p v p' replaces the pattern p' for every occurence of v inside of p
refactorPattern :: Pattern a -> Id -> Pattern a -> Pattern a
refactorPattern p@(PVar _ _ _ id) id' subpat
  | id == id' = subpat
  | otherwise = p
refactorPattern p@PWild {} _ _ = p
refactorPattern (PBox sp a _ p) id' subpat =
  let p' = refactorPattern p id' subpat
  in PBox sp a (patRefactored p') p'
refactorPattern p@PInt {} _ _ = p
refactorPattern p@PFloat {} _ _ = p
refactorPattern (PConstr sp a _ id ps) id' subpat =
  let ps' = map (\p -> refactorPattern p id' subpat) ps
  in PConstr sp a (any patRefactored ps') id ps'