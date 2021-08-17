-- Provides the desugaring step of the language

module Language.Granule.Interpreter.Desugar where

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Control.Monad.State.Strict
import Language.Granule.Syntax.SecondParameter

ppair :: Span
      -> (Pattern Type, Type)
      -> (Pattern Type, Type)
      -> (Pattern Type, Type)
ppair s (left, ty1) (right, ty2) =
    (PConstr s ty False (mkId "(,)") [left, right], ty)
  where
    ty = TyApp (TyApp (TyCon $ mkId "(,)") ty1) ty2

pairTy :: Expr v Type -> Expr v Type -> Expr v Type
pairTy e1 e2 =
   App s pty False (App s undefined False (Val s undefined False (Constr undefined (mkId "(,)") [])) e1) e2
  where
    s = nullSpanNoFile
    ty1 = getSecondParameter e1
    ty2 = getSecondParameter e2
    pty = TyApp (TyApp (TyCon $ mkId "(,)") ty1) ty2


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
desugar :: Def v Type -> Def v Type
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
      return $ Val nullSpanNoFile a False $ Abs a p (Just t1) e'
    -- Error cases
    typeDirectedDesugar (Equation s _ _ _ pats@(_ : _) e) t =
      error $ "(" <> show s
           <> "): Equation of " <> sourceName var <> " expects at least " <> show (length pats)
           <> " arguments, but signature specifies: " <> show (arity t)

    -- Fold function equations into a single case expression
    mkSingleEquation name eqs =
      Equation nullSpanNoFile name (resultType ty) False (map (\(v, ty) -> PVar nullSpanNoFile ty False v) (zip vars (parameterTypes ty)))
        (Case nullSpanNoFile (resultType ty) False guard cases)

      where
        numArgs =
          case eqs of
            ((Equation _ _ _ _ ps _):_) -> length ps
            _                           -> 0

        -- List of variables to represent each argument
        vars = [mkId (" internal" ++ show i) | i <- [1..numArgs]]

        -- Guard expression
        guard = foldl pairTy unitVal guardVars
        unitVal = Val nullSpanNoFile (tyCon "()") False (Constr (tyCon "()") (mkId "()") [])
        guardVars = map (\(var, ty) -> Val nullSpanNoFile ty False (Var ty var)) (zip vars (parameterTypes ty))

        -- case for each equation
        cases = map (\(Equation _ _ a _ pats expr) ->
           (fst $ foldl (ppair nullSpanNoFile) (PWild nullSpanNoFile (tyCon "()") False, tyCon "()") (zip pats (parameterTypes ty)), expr)) eqs
