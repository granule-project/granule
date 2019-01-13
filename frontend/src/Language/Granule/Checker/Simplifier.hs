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
  return $ normalisePred p
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
  let subst' = collectSubst p2
  p2'' <- simpl subst' p2'
  return $ removeTrivialImpls . removeTrivialIds $ (Impl ids p1' p2'')

simplifyPred' c@(Exists id k p) =
  simplifyPred' p >>= return . Exists id k

simplifyPred' c@(NegPred p) =
  simplifyPred' p >>= return . NegPred

simplifyPred' (Con c) = return (Con c)

simpl :: (?globals :: Globals)
           => Substitution -> Pred -> MaybeT Checker Pred
simpl subst p = substitute subst p >>= (return . removeTrivialImpls . removeTrivialIds)

removeTrivialImpls :: Pred -> Pred
removeTrivialImpls =
  predFold Conj remImpl Con NegPred Exists
    where remImpl _ (Conj []) p = p
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
collectSubst c@(Con (Eq _ (CVar v) (CVar v') _)) = []
collectSubst (Con (Eq _ (CVar v) c _)) = [(v, SubstC c)]
collectSubst (Con (Eq _ c (CVar v) _)) = [(v, SubstC c)]
collectSubst _ = []
