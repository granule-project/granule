{-# LANGUAGE DataKinds #-}
module Language.Granule.Synthesis.Refactor where

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Identifiers

-- Refactors an equation which contains abstractions in its equations
-- by pushing these abstractions into equation patterns
refactorEqn :: Equation v a -> Equation v a
refactorEqn (Equation sp name ref annotation pats body) =
  Equation sp name ref annotation newPats newBody
    where
      (newPats, newBody) = bubbleUpPatterns [] body pats

-- Collect patterns and rewrite beta-redexes into richer patterns
-- (first parameter is used to remember which variables originated from a box and therefore
-- which should not have their pattern matches folded into)
bubbleUpPatterns :: [Id] -> Expr v a -> [Pattern a] -> ([Pattern a], Expr v a)
-- Top-level lambda => add the pattern `p` to the list of patterns and recurse
bubbleUpPatterns gradedVars (Val _ _ _ (Abs _ p _ e)) pats =
  bubbleUpPatterns gradedVars e (pats ++ [p])


-- Handles pattern refactoring for double unboxing 
bubbleUpPatterns gradedVars (App _ _ _ (Val _ _ _ (Abs _ p@(PBox _ _ _ (PVar _ _ _ id)) _ ( (App _ _ _ (Val _ _ _ (Abs _ p'@(PBox s a rf (PVar _ _ _ id')) _ e)) (Val _ _ _ (Var _ y)))))) (Val _ _ _ (Var _ x))) pats =
  bubbleUpPatterns (id' : gradedVars) e (replaceInPats pats x (PBox s a rf p') )

-- Beta-redex whose argument is a variable and the pattern is a box pattern
-- (so also remember that `id` is now a graded variable)
bubbleUpPatterns gradedVars (App _ _ _ (Val _ _ _ (Abs _ p@(PBox _ _ _ (PVar _ _ _ id)) _ e)) (Val _ _ _ (Var _ x))) pats =
  bubbleUpPatterns (id : gradedVars) e (replaceInPats pats x p)

-- Only fold patterns on things which are linear (i.e., not from a box)
-- Beta-redex whose argument is a variable
bubbleUpPatterns gradedVars (App _ _ _ (Val _ _ _ (Abs _ p _ e)) (Val _ _ _ (Var _ x))) pats | not (x `elem` gradedVars) =
  bubbleUpPatterns gradedVars e (replaceInPats pats x p)

-- In the case the `x` came from an unboxing pattern, skip over this beta redex
bubbleUpPatterns gradedVars (App s a b (Val s' a' b' (Abs s'' p mt e)) (Val s3 a3 b3 (Var a4 x))) pats =
  let
    (pats', e') = bubbleUpPatterns gradedVars e pats
  in
    (pats', App s a b (Val s' a' b' (Abs s'' p mt e')) (Val s3 a3 b3 (Var a4 x)))

-- Fold away case expressions
bubbleUpPatterns gradedVars (Case _ _ _ (Val _ _ _ (Var _ name)) [(p, expr)]) pats =
  bubbleUpPatterns gradedVars expr (replaceInPats pats name p)

bubbleUpPatterns _ e pats = (pats, e)

refactorCase :: Eq a => [Pattern a] -> Expr v a -> [([Pattern a], Expr v a)]
refactorCase pats (Case _ _ _ (Val _ _ _ (Var _ name)) casePats) =
  concatMap (\(pat, body) -> refactorCase (replaceInPats pats name pat) body) casePats
refactorCase pats (Case _ _ _ (Val _ _ _ (Promote _ (Val _ _ _ (Var _ name)))) casePats) =
  concatMap (\(pat, body) -> refactorCase (replaceInPats pats name pat) body) casePats
refactorCase pats e = [(pats, e)]

-- Refactors a case expression to pattern match on the ADT at the function equation level
refactorCaseEqn :: Eq a => Equation v a -> [Equation v a]
refactorCaseEqn (Equation sp name ref ant pats body) =
  let refactors = refactorCase pats body in
  map (\(x,y) -> Equation sp name ref ant x y) refactors

-- Refactors a pattern by traversing to the rewritten variable and replacing
-- -- the variable with the subpattern.
replaceInPats :: [Pattern a] -> Id -> Pattern a -> [Pattern a]
replaceInPats pats var pat' = map (\pat -> refactorPattern pat var pat') pats

-- refactorPattern p v p' replaces the pattern p' for every occurence of v inside of p
refactorPattern :: Pattern a -> Id -> Pattern a -> Pattern a
refactorPattern p@(PVar _ _ _ id) id' subpat
  | id == id' = subpat
  | otherwise = p
refactorPattern p@PWild {} _ _ = p
refactorPattern (PBox sp a b p) id' (PBox sp' a' b' p') =
   let p'' = refactorPattern p id' p'
   in PBox sp a (patRefactored p') p''
refactorPattern (PBox sp a b p) id' subpat =
   let p' = refactorPattern p id' subpat
   in PBox sp a (patRefactored p') p'
refactorPattern p@PInt {} _ _ = p
refactorPattern p@PFloat {} _ _ = p
refactorPattern (PConstr sp a _ id ps) id' subpat =
  let ps' = map (\p -> refactorPattern p id' subpat) ps
  in PConstr sp a (any patRefactored ps') id ps'