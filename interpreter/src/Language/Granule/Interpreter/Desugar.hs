-- Provides the desugaring step of the interpreter

module Language.Granule.Interpreter.Desugar where

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Control.Monad.State.Strict

{- | 'desugar' pushes function-equation pattern matches inside the
      function as lambda bindings and `case` expressions.

   This is used to simplify the operational semantics and compilation.

   e.g., for a definition 'd' in code as:
         f : Int [1] -> ...
         f [x] = e

    then desugar d produces
         f : Int [1] -> ...
         f = \([x] : Int [1]) -> e

   Note that the explicit typing from the type signature is pushed
   inside of the definition to give an explicit typing on the abstraction -}
desugar :: Def v () -> Def v ()
-- desugar adt@ADT{} = adt
desugar (Def s var rf eqs tys@(Forall _ _ _ ty)) =
  Def s var rf (EquationList s var rf [typeDirectedDesugarEquation (mkSingleEquation var (equations eqs))]) tys
  where
    typeDirectedDesugarEquation (Equation s name a rf ps body) =
      Equation s name a rf []
        -- Desugar the body
        (evalState (typeDirectedDesugar (Equation s name a rf ps body) ty) (0 :: Int))

    typeDirectedDesugar (Equation _ _ _ _ [] e) _ = return e
    typeDirectedDesugar (Equation s name a rf (p : ps) e) (FunTy _ t1 t2) = do
      e' <- typeDirectedDesugar (Equation s name a rf ps e) t2
      return $ Val nullSpanNoFile () False $ Abs () p (Just t1) e'
    -- Error cases
    typeDirectedDesugar (Equation s _ _ _ pats@(_ : _) e) t =
      error $ "(" <> show s
           <> "): Equation of " <> sourceName var <> " expects at least " <> show (length pats)
           <> " arguments, but signature specifies: " <> show (arity t)

    -- Fold function equations into a single case expression
    mkSingleEquation name eqs =
      Equation nullSpanNoFile name () False (map (PVar nullSpanNoFile () False) vars)
        (Case nullSpanNoFile () False guard cases)

      where
        numArgs =
          case eqs of
            ((Equation _ _ _ _ ps _):_) -> length ps
            _                         -> 0

        -- List of variables to represent each argument
        vars = [mkId (" internal" ++ show i) | i <- [1..numArgs]]

        -- Guard expression
        guard = foldl1 pair guardVars
        guardVars = map (\i -> Val nullSpanNoFile () False (Var () i)) vars

        -- case for each equation
        cases = map (\(Equation _ _ _ _ pats expr) ->
           (foldl1 (ppair nullSpanNoFile ()) pats, expr)) eqs
