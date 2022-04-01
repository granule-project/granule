{-# LANGUAGE ImplicitParams #-}

-- | Simplifier for predicates (useful for error messages)
module Language.Granule.Checker.Simplifier where

import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Helpers (freeVars)
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Monad

import Language.Granule.Utils

import Data.List (nub)
import Data.Maybe (catMaybes)

allCons :: [Pred] -> Bool
allCons = all (\p -> case p of Con _ -> True; _ -> False)

simplifyPred :: (?globals :: Globals)
             => Pred -> Checker Pred
simplifyPred p = go 10 p
  where
    -- Bounded fixed-point (don't go for ever, in case things are non-converging somehow)
    go 0 p = return p
    go n p = do
      p <- simplifyPred' p
      let p' = flatten $ normalisePred p
      if (p == p') then return p' else go (n-1) p'

    normalisePred = predFold
       Conj Disj Impl (Con . normaliseConstraint) NegPred Exists

simplifyPred' :: (?globals :: Globals)
             => Pred -> Checker Pred

simplifyPred' (Conj ps) = do
  -- Collect any substitutions implied by the constraints
  let subst = collectSubst (Conj ps)
  -- Apply these subsitutions to the conjunction
  (Conj ps') <- simpl subst (Conj ps)
  -- Then recursively apply the simplification to each subpart
  ps' <- mapM simplifyPred' ps'
  -- Remove any duplications
  let ps'' = nub ps'
  -- Output the final conjunction
  if length ps'' == 1
    then return $ head ps''
    else return $ Conj ps''

simplifyPred' (Disj ps) = do
  ps <- mapM simplifyPred' ps
  return $ Disj ps

simplifyPred' c@(Impl ids p1 p2) = do
  let subst = collectSubst p1
  p1' <- simpl subst p1
  p2' <- simpl subst p2
  let subst' = collectSubst p2'
  p2'' <- simpl subst' p2'
  return $ removeTrivialImpls . removeTrivialIds $ (Impl ids p1' p2'')

simplifyPred' c@(Exists id k p) = do
  p' <- simplifyPred' p
  -- Strip quantifications that are no longer used
  if id `elem` (freeVars p')
    then return $ Exists id k p'
    else return p'

simplifyPred' c@(NegPred p) =
  simplifyPred' p >>= return . NegPred

simplifyPred' (Con c) = return (Con c)

flatten :: Pred -> Pred
flatten (Conj []) = Conj []
flatten (Conj ((Conj []):ps)) = flatten (Conj ps)
flatten (Conj (p : ps)) =
  case flatten p of
    Conj [] -> flatten (Conj ps)
    p'      -> case flatten (Conj ps) of
                Conj ps' -> Conj (p' : ps')
                p'' -> Conj [p, p'']
flatten (Disj ps) =
  Disj (map flatten ps)
flatten (Impl ids p1 p2) =
  Impl ids (flatten p1) (flatten p2)
flatten (Exists v k p) = Exists v k (flatten p)
flatten (NegPred p) = NegPred (flatten p)
flatten (Con c) = Con c


simpl :: (?globals :: Globals)
           => Substitution -> Pred -> Checker Pred
simpl subst p = substitute subst p >>= (return . removeTrivialImpls . removeTrivialIds)

removeTrivialImpls :: Pred -> Pred
removeTrivialImpls =
  predFold (Conj . nub) Disj remImpl Con NegPred Exists
    where remImpl _ (Conj []) p = p
          remImpl _ (Conj ps) p | all (\p -> case p of Conj [] -> True; _ -> False) ps = p
          remImpl ids p1 p2 = Impl ids p1 p2

removeTrivialIds :: Pred -> Pred
removeTrivialIds =
  predFold conj disj Impl conRemove NegPred Exists
    where removeTrivialIdCon (Con (Eq _ c c' _)) | c == c' = Nothing
          -- removeTrivialIdCon (Con (ApproximatedBy _ c c' _)) | c == c' = Nothing
          removeTrivialIdCon c = Just c

          conj ps = Conj $ catMaybes (map removeTrivialIdCon ps)
          disj ps =
            if (catMaybes (map removeTrivialIdCon ps) == ps)
              then Disj ps
              else Conj []

          conRemove c =
            case removeTrivialIdCon (Con c) of
              Nothing -> Conj []
              Just  c -> c

collectSubst :: Pred -> Substitution
collectSubst (Conj ps) = concatMap collectSubst ps
-- For a pair of variables, substitute the right for the left
collectSubst (Con (Eq _ (TyVar v1) (TyVar v2) _)) = [(v1, SubstT (TyVar v2))]
collectSubst (Con (Eq _ (TyVar v) c _)) = [(v, SubstT c)]
collectSubst (Con (Eq _ c (TyVar v) _)) = [(v, SubstT c)]
collectSubst _ = []
