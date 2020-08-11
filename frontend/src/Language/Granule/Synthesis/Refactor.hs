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
  Equation sp name ref annotation (pats ++ getPatterns body) (exprBody body)
    where
      getPatterns e = boxPatterns e (exprPatterns e)

      replace (pat@(PVar _ _ _ name):xs) var pat' =
        if name == var then
          (pat' : (replace xs var pat'))
        else
          (pat : (replace xs var pat'))
      replace (pat@(PBox {}):xs) var pat' =
        pat : (replace xs var pat')
      replace ((PConstr s ty a id constrs):xs) var pat' =
        (PConstr s ty a id (replace constrs var pat')) : replace xs var pat'
      replace pats _ _ = pats

      exprPatterns (App _ _ _ (Val _ _ _ (Abs _ p _ e )) _) = exprPatterns e
      exprPatterns (Val _ _ _ (Abs _ p _ e)) = p  : exprPatterns e
      exprPatterns e = []

      boxPatterns (Val _ _ _ (Abs _ p _ e)) pats = boxPatterns e pats
      boxPatterns (App _ _ _ (Val _ _ _ (Abs _ p _ e )) (Val _ _ _ (Var _ name))) pats =
        boxPatterns e pats'
         where
          pats' = replace pats name p
      boxPatterns e pats = pats

      exprBody (App _ _ _ (Val _ _ _ (Abs _ _ _ e )) _) = exprBody e
      exprBody (Val _ _ _ (Abs _ _ _ e)) = exprBody e
      exprBody e = e


refactorCase :: Eq a => [Pattern a] -> Expr v a -> [([Pattern a], Expr v a)]
refactorCase pats (Case _ _ _ (Val _ _ _ (Var _ name)) casePats) =
  case checkPatternId name pats of
    Just (p, pats') -> concatMap (doCasePat pats') casePats
    _ -> concatMap (doCasePat pats) casePats
refactorCase pats expr = [(pats, expr)]

-- Refactors a case expression to pattern match on the ADT at the function equation level
refactorCaseEqn :: Eq a => Equation v a -> [Equation v a]
refactorCaseEqn (Equation sp name ref ant pats body) =
  let refactors = refactorCase pats body in
  map (\(x,y) -> Equation sp name ref ant x y)  refactors

doCasePat :: Eq a => [Pattern a] -> (Pattern a, Expr v a) -> [([Pattern a], Expr v a)]
doCasePat totalPats (casePat, caseExpr) =
  refactorCase (casePat:totalPats) caseExpr

-- Given an Id and a list of patterns, return the pattern with the same Id and the remainder
checkPatternId :: Id -> [Pattern a] -> Maybe ((Pattern a), [Pattern a])
checkPatternId id (p@(PVar _ _ _ id'):rest) =
  if id == id' then
    Just (p, rest)
  else
    do
      (p', rest') <- checkPatternId id rest
      return (p', p:rest')
checkPatternId id (p@(PConstr _ _ _ id' _):rest) =
  if id == id' then
    Just (p, rest)
  else
    do
      (p', rest') <- checkPatternId id rest
      return (p', p:rest')
checkPatternId id (p@(PBox _ _ _ p'):rest) = do
  (p'', rest') <- checkPatternId id (p':rest)
  return  (p'', p:rest')
checkPatternId id _ = Nothing

