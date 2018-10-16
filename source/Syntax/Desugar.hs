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
         f = \|x| : Int -> e

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
      e' <- typeDirectedDesugar ps t2 e
      return $ Val nullSpan $ Abs p (Just t1) e'
    -- Error cases
    typeDirectedDesugar (_ : _) t e =
      error $ "(" <> show sl <> "," <> show sc
           <> "): Definition of " <> sourceName var <> " expects at least " <> show (length pats)
           <> " arguments, but signature specifies: " <> show (arity t)
      where ((sl, sc), _) = getSpan e
