-- Provides the desugaring step of the language

module Syntax.Desugar where

import Syntax.Expr
import Control.Monad.State.Strict

{- | 'desugar' erases pattern matches in function definitions
   with coeffect binders.
   This is used to simplify the operational semantics and compilation (future).

   e.g., for a definition 'd' in code as:
         f : Int |1| -> ...
         f |x| = e

    then desugar d produces
         f : Int |1| -> ...
         f xFresh = let |x| : Int = xFresh in e

   Note that the explicit typing from the type signature is pushed
   inside of the definition to give an explicit typing on the coeffect-let
   binding. -}
desugar :: Def -> Def
-- desugar adt@ADT{} = adt
desugar (Def s var expr pats tys@(Forall _ _ ty)) =
  Def s var (evalState (typeDirectedDesugar pats ty expr) (0 :: Int)) [] tys
  where
    typeDirectedDesugar [] _ e = return e
    typeDirectedDesugar (p : ps) (FunTy t1 t2) e = do
      v  <- freshVar
      eT <- desugarPattern v p t1
      e' <- typeDirectedDesugar ps t2 e
      return $ Val nullSpan $ Abs (PVar nullSpan v) (Just t1) (eT e')
    -- Error cases
    typeDirectedDesugar (_ : _) t e = do
      error $ "(" ++ show sl ++ "," ++ show sc
           ++ "): Definition of " ++ sourceName var ++ " expects at least " ++ show (length pats)
           ++ " arguments, but signature specifies: " ++ show (arity t)
      where ((sl, sc), _) = getSpan e

{- | `desugarPattern v p t` desugars a pattern match `p` made on a
        variable `v` of type `t` which provides an expression
        transformer: Expr -> Expr which wraps an expression in the
        desugaring of the pattern match `p` on `v`.

        This is stateful, with a fresh name genertor.

        *Pre-condition: type checking has been performed and so this
         always succeeds* -}
desugarPattern ::  Id -> Pattern -> Type -> State Int (Expr -> Expr)
desugarPattern _ (PWild _) _ = return id
desugarPattern v (PVar _ v') _ =
  -- Desugars to: (\v' -> e) v
  return $ \e -> App nullSpan
                   (Val nullSpan (Abs (PVar nullSpan v') Nothing e))
                     (Val nullSpan (Var v))

desugarPattern v (PPair _ p1 p2) (PairTy _ _) =
  -- Desguars to: case v of (p1, p2) -> e
  return $ \e -> Case nullSpan (Val nullSpan (Var v)) [(PPair nullSpan p1 p2, e)]

desugarPattern v (PBox _ (PVar _ v')) (Box _ t) =
  -- Speciale case of a box pattern with a variable inside
  -- Desugars to: let |v| : t in e
  return $ \e -> letBox nullSpan (PVar nullSpan v') (Just t)
                                  (Val nullSpan (Var v)) e

desugarPattern v (PBox _ p) (Box _ t) = do
  -- General case of a box pattern
  -- Desugars to: let |v'| : t = v in (desugarPattern v' p t)
  v' <- freshVar
  eT <- desugarPattern v' p t
  return $ \e -> letBox nullSpan (PVar nullSpan v') (Just t)
                                 (Val nullSpan (Var v)) (eT e)

desugarPattern v p _ =
  -- Fall-back case is to replace with a 'case' pattern
  return $ \e -> Case nullSpan (Val nullSpan (Var v)) [(p, e)]

freshVar :: State Int Id
freshVar = do
  n <- get
  put (n+1)
  return . mkId $ "eval v" ++ show n
