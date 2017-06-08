-- Provides the desugaring step of the language

module Syntax.Desugar where

import Syntax.Expr
import Control.Monad.State.Strict

desugar :: Def -> Def
desugar (Def var expr pats ty) =
  Def var (evalState (desguarPats expr pats ty []) (0 :: Int)) [] ty
  where
    unfoldBoxes [] e = e
    unfoldBoxes ((v, v', t) : binds) e =
      LetBox v t (Val $ Var v') (unfoldBoxes binds e)

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

    desguarPats e (PBoxVar v : ps) (FunTy (Box _ t) t2) boxed = do
      n <- get
      let v' = v ++ show n
      put (n + 1)
      e' <- desguarPats e ps t2 (boxed ++ [(v, v', t)])
      return $ Val $ Abs v' e'

    desguarPats _ _ _ _ = error $ "Definition of " ++ var ++ "expects at least " ++
                      show (length pats) ++ " arguments, but signature " ++
                      " specifies: " ++ show (arity ty)
