-- Provides the desugaring step of the language

module Syntax.Desugar where

import Syntax.Expr
import Checker.Coeffects
import Control.Monad.State.Strict

desugar :: Def -> Def
desugar (Def var expr pats tys@(Forall ckinds ty)) =
  Def var (evalState (desguarPats expr pats ty []) (0 :: Int)) [] tys
  where
    unfoldBoxes [] e = e
    unfoldBoxes ((v, v', t, k) : binds) e =
      LetBox v t k (Val $ Var v') (unfoldBoxes binds e)

    desguarPats e [] _ boxed =
      return $ unfoldBoxes boxed e

    desguarPats e (PWild : ps) (FunTy _ t2) boxed = do
      -- Create a fresh variable to use in the lambda
      -- since lambda doesn't support pattern matches
      n <- get
      let v' = show n
      put (n + 1)
      e' <- desguarPats e ps t2 boxed
      return $ Val $ Abs v' e'

    desguarPats e (PVar v : ps) (FunTy _ t2) boxed = do
      e' <- desguarPats e ps t2 boxed
      return $ Val $ Abs v e'

    desguarPats e (PBoxVar v : ps) (FunTy (Box c t) t2) boxed = do
      n <- get
      let v' = v ++ show n
      put (n + 1)
      e' <- desguarPats e ps t2 (boxed ++ [(v, v', t, kindOf c ckinds)])
      return $ Val $ Abs v' e'

    desguarPats _ _ _ _ = error $ "Definition of " ++ var ++ "expects at least " ++
                      show (length pats) ++ " arguments, but signature " ++
                      " specifies: " ++ show (arity ty)
