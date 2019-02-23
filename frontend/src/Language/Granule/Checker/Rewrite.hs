{- |
Module      :  Language.Granule.Checker.Rewrite
Description :  Rewrite a type-annotated AST to an intermediate representation

Rewrites a type-annotated AST to an intermediate representation
without interfaces.
-}


{-# LANGUAGE ImplicitParams #-}
module Language.Granule.Checker.Rewrite
    ( rewriteWithoutInterfaces
    ) where


import Control.Arrow ((***))
import Control.Monad.State (evalState)
import Data.List (foldl', groupBy)

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Type

import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Utils

import Language.Granule.Checker.Rewrite.Type


-- | Generate a fresh dictionary variable for an instance.
freshDictName :: (?globals :: Globals) => Id -> IFaceDat -> Rewriter Id
freshDictName name idat = pure . mkId $ "$" <> pretty name <> "(" <> pretty idat <> ")"


-- | Get the name of the dictionary type constructor for the interface.
getDictTyCon :: (?globals :: Globals) => Id -> Rewriter Type
getDictTyCon n = pure $ TyCon (mkId $ "$" <> pretty n <> "Dict")


-- | Get the name of the dictionary data constructor for the interface.
getDictDataCon :: (?globals :: Globals) => Id -> Rewriter (Expr v ())
getDictDataCon n = pure $ Val nullSpanNoFile () $ Constr () (mkId $ "$Mk" <> pretty n <> "Dict") []


------------------------
----- AST Rewriter -----
------------------------


-- | Rewrite a type-annotated AST to an intermediate
-- | representation without interfaces.
rewriteWithoutInterfaces :: (?globals :: Globals, Pretty v) => RewriteEnv -> AST v a -> Either RewriterError (AST v ())
rewriteWithoutInterfaces renv ast =
    let (AST dds defs _ insts) = forgetAnnotations ast
    in runNewRewriter (do instsToDefs <- mapM mkInst insts
                          pure $ AST dds (instsToDefs <> defs) [] []) renv


-- | Forget the AST's annotations.
forgetAnnotations :: AST v a -> AST v ()
forgetAnnotations = mapAnnotations (const ())


-- | Map over an AST's annotations.
mapAnnotations :: (a -> b) -> AST v a -> AST v b
mapAnnotations f (AST dds defs ifaces insts) =
    AST dds (fmap mapDefAnnotations defs) ifaces (fmap mapInstanceAnnotations insts)
    where mapDefAnnotations (Def s n eqs tys) = Def s n (fmap mapEquationAnnotations eqs) tys

          mapEquationAnnotations (Equation s ann pats expr) =
              Equation s (f ann) (fmap mapPatternAnnotations pats) (mapExprAnnotations expr)

          mapPatternAnnotations (PVar s ann n) = PVar s (f ann) n
          mapPatternAnnotations (PWild s ann) = PWild s (f ann)
          mapPatternAnnotations (PBox s ann pat) = PBox s (f ann) (mapPatternAnnotations pat)
          mapPatternAnnotations (PInt s ann v) = PInt s (f ann) v
          mapPatternAnnotations (PFloat s ann v) = PFloat s (f ann) v
          mapPatternAnnotations (PConstr s ann n pats) = PConstr s (f ann) n (fmap mapPatternAnnotations pats)

          mapExprAnnotations (App s ann e1 e2) = App s (f ann) (mapExprAnnotations e1) (mapExprAnnotations e2)
          mapExprAnnotations (Binop s ann op l r) = Binop s (f ann) op (mapExprAnnotations l) (mapExprAnnotations r)
          mapExprAnnotations (LetDiamond s ann pat mty e1 e2) =
              LetDiamond s (f ann) (mapPatternAnnotations pat) mty (mapExprAnnotations e1) (mapExprAnnotations e2)
          mapExprAnnotations (Val s ann v) = Val s (f ann) (mapValueAnnotations v)
          mapExprAnnotations (Case s ann sw ar) =
              Case s (f ann) (mapExprAnnotations sw) (fmap (mapPatternAnnotations *** mapExprAnnotations) ar)

          mapValueAnnotations (Abs ann pat t expr) = Abs (f ann) (mapPatternAnnotations pat) t (mapExprAnnotations expr)
          mapValueAnnotations (Promote ann expr) = Promote (f ann) (mapExprAnnotations expr)
          mapValueAnnotations (Pure ann expr) = Pure (f ann) (mapExprAnnotations expr)
          mapValueAnnotations (Constr ann n vs) = Constr (f ann) n (fmap mapValueAnnotations vs)
          mapValueAnnotations (Var ann n) = Var (f ann) n
          mapValueAnnotations (NumInt n) = NumInt n
          mapValueAnnotations (NumFloat n) = NumFloat n
          mapValueAnnotations (CharLiteral c) = CharLiteral c
          mapValueAnnotations (StringLiteral s) = StringLiteral s
          mapValueAnnotations (Ext ann extv) = Ext (f ann) extv

          mapInstanceAnnotations (Instance s n constrs idat idefs) =
              Instance s n constrs idat (fmap mapIDefAnnotations idefs)

          mapIDefAnnotations (IDef s n eq) = IDef s n (mapEquationAnnotations eq)


-- | Rewrite an instance to its intermediate representation.
--
-- @
--   instance Bar A where
--     bar1 Av = Av
--     bar2 = Av
-- @
--
-- becomes:
--
-- @
--   barA : BarDict A
--   barA = MkBarDict [fooA] [\Av -> Av] [Av]
-- @
mkInst :: (?globals :: Globals, Pretty v) => Instance v () -> Rewriter (Def v ())
mkInst inst@(Instance sp iname _constrs idt@(IFaceDat _ ty) _) = do
    dictName <- freshDictName iname idt
    idictTyCon <- getDictTyCon iname
    idictConstructed <- constructIDict inst
    let tys = Forall sp [] [] (TyApp idictTyCon ty)
        def = Def sp dictName [Equation sp () [] idictConstructed] tys
    pure def


getInstanceGrouped :: Instance v a -> Rewriter [(Id, TypeScheme, [Equation v a])]
getInstanceGrouped inst@(Instance _ _ _ _ ds) = do
  let nameGroupedDefs = groupBy
        (\(IDef _ name1 _) (IDef _ name2 _) ->
          name1 == name2 || name2 == Nothing) ds
      groupedEqns = map
        (\((IDef _ (Just name) eq):dt) ->
          let eqs = map (\(IDef _ _ eqn) -> eqn) dt
          in (name, eq:eqs)) nameGroupedDefs
  mapM (\(name, eqns) -> do
          ty <- getInstanceMethTys (mkInstanceId inst) name
          pure (name, ty, eqns)) groupedEqns


-- | Construct an expression that builds an appropriate dictionary
-- | instance for the interface.
constructIDict :: (?globals :: Globals) => Instance v () -> Rewriter (Expr v ())
constructIDict inst@(Instance _ iname _ _ _) = do
  idictDataCon <- getDictDataCon iname

  grouped <- getInstanceGrouped inst
  let lambdas = fmap desugarIdef grouped
      dictApp = foldl' (App nullSpanNoFile ()) idictDataCon lambdas
  pure dictApp
    where
      desugarIdef (_, t, eqns) = desugar eqns t


-- | Produce a lambda expression from a set of equations and a typescheme.
desugar :: [Equation v ()] -> TypeScheme -> Expr v ()
desugar eqs (Forall _ _ _ ty) =
  typeDirectedDesugarEquation mkSingleEquation
  where
    typeDirectedDesugarEquation (Equation _ _ ps body) =
        -- Desugar the body
        (evalState (typeDirectedDesugar ps body ty) (0 :: Int))

    typeDirectedDesugar [] e _ = return e
    typeDirectedDesugar (p : ps) e (FunTy t1 t2) = do
      e' <- typeDirectedDesugar ps e t2
      return $ Val nullSpanNoFile () $ Abs () p (Just t1) e'
    typeDirectedDesugar _ _ _ = error "internal error: Rewriter.desugar"
    -- Fold function equations into a single case expression
    mkSingleEquation =
      Equation nullSpanNoFile () (map (PVar nullSpanNoFile ()) vars)
        (Case nullSpanNoFile () guard cases)

      where
        numArgs = case head eqs of Equation _ _ ps _ -> length ps

        -- List of variables to represent each argument
        vars = [mkId ("$internal" ++ show i) | i <- [1..numArgs]]

        -- Guard expression
        guard = foldl (pair nullSpanNoFile) unitVal guardVars
        unitVal = Val nullSpanNoFile () (Constr () (mkId "()") [])
        guardVars = map (\i -> Val nullSpanNoFile () (Var () i)) vars

        -- case for each equation
        cases = map (\(Equation _ _ pats expr) ->
           (foldl (ppair nullSpanNoFile) (PWild nullSpanNoFile ()) pats, expr)) eqs
