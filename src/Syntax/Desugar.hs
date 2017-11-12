-- Provides the desugaring step of the language

module Syntax.Desugar where

import Syntax.Expr
import Control.Monad.State.Strict

-- 'desugar' erases pattern matches in function definitions
-- with coeffect binders.
-- e.g., for a definition 'd' in code as:
--       f : Int |1| -> ...
--       f |x| = e
--
--  then desugar d produces
--       f : Int |1| -> ...
--       f xFresh = let |x| : Int = xFresh in e
--
-- Note that the explicit typing from the type signature is pushed
-- inside of the definition to give an explicit typing on the coeffect-let
-- binding.
desugar :: Def -> Def
desugar (Def s var expr pats tys@(Forall _ _ ty)) =
  Def s var (evalState (desugarPats expr pats ty []) (0 :: Int)) [] tys
  where
    unfoldBoxes [] e = e
    unfoldBoxes ((v, v', t, sp) : binds) e =
      LetBox (getSpan e) v t (Val sp $ Var v') (unfoldBoxes binds e)

    desugarPats e [] _ boxed =
      return $ unfoldBoxes boxed e

    desugarPats e (PWild _ : ps) (FunTy t1 t2) boxed = do
      -- Create a fresh variable to use in the lambda
      -- since lambda doesn't support pattern matches
      n <- get
      let v' = show n
      put (n + 1)
      e' <- desugarPats e ps t2 boxed
      return $ Val (getSpan e) $ Abs v' (Just t1) e'

    desugarPats e (PVar _ v : ps) (FunTy t1 t2) boxed = do
      e' <- desugarPats e ps t2 boxed
      return $ Val (getSpan e) $ Abs v (Just t1) e'

    desugarPats e (PBox _ (PWild _) : ps) (FunTy (Box c t) t2) boxed = do
      n <- get
      let v' = show n
      put (n + 1)
      e' <- desugarPats e ps t2 (boxed ++ [("", v', t, s)])
      return $ Val (getSpan e) $ Abs v' (Just (Box c t)) e'

    desugarPats e (PBox _ (PVar _ v) : ps) (FunTy (Box c t) t2) boxed = do
      n <- get
      let v' = v ++ show n
      put (n + 1)
      e' <- desugarPats e ps t2 (boxed ++ [(v, v', t, s)])
      return $ Val (getSpan e) $ Abs v' (Just (Box c t)) e'

    desugarPats e (PPair _ p1 p2 : ps) (FunTy (PairTy t1 t2) t3) boxed = do
      n <- get
      let v' = show n
      put (n+1)
      e' <- desugarPats e ps t3 boxed
      return $ Val (getSpan e) $
        Abs v' Nothing (Case nullSpan (Val nullSpan (Var v')) [(PPair nullSpan p1 p2, e')])

    desugarPats e _ _ _ =
      error $ "Type error at line " ++ show sl ++ ", column " ++ show sc
           ++ ": Definition of " ++ var ++ " expects at least " ++ show (length pats)
           ++ " arguments, but signature specifies: " ++ show (arity ty)
      where ((sl, sc), _) = getSpan e
