{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.Simplifier where

import Control.Monad.Trans.Maybe

import Language.Granule.Syntax.Type
import Language.Granule.Checker.Substitutions
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Monad

import Language.Granule.Utils

import Data.Maybe (catMaybes)

allCons :: [Pred] -> Bool
allCons = all (\p -> case p of Con _ -> True; _ -> False)

simplifyPred :: (?globals :: Globals)
             => Pred -> MaybeT Checker Pred
simplifyPred p = do
  p <- simplifyPred' p
  return $ flatten $ normalisePred p
  where
    normalisePred = predFold
       Conj Impl (Con . normaliseConstraint) NegPred Exists

simplifyPred' :: (?globals :: Globals)
             => Pred -> MaybeT Checker Pred
simplifyPred' c@(Conj ps) | allCons ps =
  simpl subst c where subst = collectSubst c

simplifyPred' (Conj ps) = do
  ps <- mapM simplifyPred' ps
  return $ Conj ps

simplifyPred' c@(Impl ids p1 p2) = do
  let subst = collectSubst p1
  p1' <- simpl subst p1
  p2' <- simpl subst p2
  let subst' = collectSubst p2'
  p2'' <- simpl subst' p2'
  return $ removeTrivialImpls . removeTrivialIds $ (Impl ids p1' p2'')

simplifyPred' c@(Exists id k p) =
  simplifyPred' p >>= return . Exists id k

simplifyPred' c@(NegPred p) =
  simplifyPred' p >>= return . NegPred

simplifyPred' (Con c) = return (Con c)

flatten :: Pred -> Pred
flatten (Conj []) = Conj []
flatten (Conj ((Conj []):ps)) =
 flatten (Conj ps)
flatten (Conj (p : ps)) =
  case flatten p of
    Conj [] -> flatten (Conj ps)
    p'      -> case flatten (Conj ps) of
                Conj ps' -> Conj (p' : ps')
                p'' -> Conj [p, p'']
flatten (Impl ids p1 p2) =
  Impl ids (flatten p1) (flatten p2)
flatten (Exists v k p) = Exists v k (flatten p)
flatten (NegPred p) = NegPred (flatten p)
flatten (Con c) = Con c


simpl :: (?globals :: Globals)
           => Substitution -> Pred -> MaybeT Checker Pred
simpl subst p = substitute subst p >>= (return . removeTrivialImpls . removeTrivialIds)

removeTrivialImpls :: Pred -> Pred
removeTrivialImpls =
  predFold Conj remImpl Con NegPred Exists
    where remImpl _ (Conj []) p = p
          remImpl _ (Conj ps) p | all (\p -> case p of Conj [] -> True; _ -> False) ps = p
          remImpl ids p1 p2 = Impl ids p1 p2

removeTrivialIds :: Pred -> Pred
removeTrivialIds =
  predFold conj Impl conRemove NegPred Exists
    where removeTrivialIdCon (Con (Eq _ c c' _)) | c == c' = Nothing
          removeTrivialIdCon c = Just c

          conj ps = Conj $ catMaybes (map removeTrivialIdCon ps)
          conRemove c =
            case removeTrivialIdCon (Con c) of
              Nothing -> Conj []
              Just  c -> c

collectSubst :: Pred -> Substitution
collectSubst (Conj ps) = concatMap collectSubst ps
collectSubst (Con (Eq _ (CVar v) c _)) = [(v, SubstC c)]
collectSubst (Con (Eq _ c (CVar v) _)) = [(v, SubstC c)]
collectSubst _ = []
