-- Provides the desugaring step of the language

module Language.Granule.Desugar where

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
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
desugar :: Show v => Def v () -> Def v ()
-- desugar adt@ADT{} = adt
desugar (Def s var eqs tys@(Forall _ _ _ ty)) =
  Def s var [typeDirectedDesugarEquation (mkSingleEquation eqs)] tys
  where
    typeDirectedDesugarEquation (Equation s a ps body) =
      Equation s a []
        -- Desugar the body
        (evalState (typeDirectedDesugar (Equation s a ps body) ty) (0 :: Int))

    typeDirectedDesugar (Equation _ _ [] e) _ = return e
    typeDirectedDesugar (Equation s a (p : ps) e) (FunTy t1 t2) = do
      e' <- typeDirectedDesugar (Equation s a ps e) t2
      return $ Val nullSpanNoFile () $ Abs () p (Just t1) e'
    -- Error cases
    typeDirectedDesugar (Equation s _ pats@(_ : _) e) t =
      error $ "(" <> show s
           <> "): Equation of " <> sourceName var <> " expects at least " <> show (length pats)
           <> " arguments, but signature specifies: " <> show (arity t)

    -- Fold function equations into a single case expression
    mkSingleEquation eqs =
      Equation nullSpanNoFile () (map (PVar nullSpanNoFile ()) vars)
        (Case nullSpanNoFile () guard cases)

      where
        numArgs = case head eqs of Equation _ _ ps _ -> length ps

        -- List of variables to represent each argument
        vars = [mkId (" internal" ++ show i) | i <- [1..numArgs]]

        -- Guard expression
        guard = foldl pair unitVal guardVars
        unitVal = Val nullSpanNoFile () (Constr () (mkId "()") [])
        guardVars = map (\i -> Val nullSpanNoFile () (Var () i)) vars

        -- case for each equation
        cases = map (\(Equation _ _ pats expr) ->
           (foldl (ppair nullSpanNoFile ()) (PWild nullSpanNoFile ()) pats, expr)) eqs
