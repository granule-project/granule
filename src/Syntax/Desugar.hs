-- Provides the desugaring step of the language

module Syntax.Desugar where

import Syntax.Expr
import Data.List
import Control.Monad.State.Strict

desugar :: Def -> Def
desugar (Def id e pats ty) =
  Def id (evalState (desguarPats e pats ty []) 0) [] ty
  where
    unfoldBoxes [] e = e
    unfoldBoxes ((v, v', t) : binds) e =
      LetBox v t (Var v') (unfoldBoxes binds e)

    desguarPats e [] _ boxed =
      return $ unfoldBoxes boxed e

    desguarPats e (Left v : pats) (FunTy _ t2) boxed = do
      e' <- desguarPats e pats t2 boxed
      return $ Abs v e'

    desguarPats e (Right v : pats) (FunTy (Box _ t) t2) boxed = do
      n <- get
      let v' = v ++ show n
      put (n + 1)
      e' <- desguarPats e pats t2 (boxed ++ [(v, v', t)])
      return $ Abs v' e'

    desguarPats e _ _ _ = error $ "Definition of " ++ id ++ "expects at least " ++
                      show (length pats) ++ " arguments, but signature " ++
                      " specifies: " ++ show (arity ty)
