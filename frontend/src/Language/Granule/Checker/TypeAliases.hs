module Language.Granule.Checker.TypeAliases where

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Expr
import Language.Granule.Checker.Primitives (typeAliases)

import Data.Functor.Identity (runIdentity)

replaceTypeAliases :: AST a b -> AST a b
replaceTypeAliases (AST dataDecls defs imports hidden name) =
  AST
    (map replaceInDataDecl dataDecls)
    (map replaceInDef defs)
    imports hidden name

replaceInDataDecl :: DataDecl -> DataDecl
replaceInDataDecl (DataDecl s v tyVarContext kindAnn constrs) =
 DataDecl s v (map (\(id, t) -> (id, replaceInType t)) tyVarContext)
   (replaceInMaybeType kindAnn)
   (map replaceInDataConstr constrs)

replaceInDataConstr :: DataConstr -> DataConstr
replaceInDataConstr (DataConstrIndexed s v tySch) =
  DataConstrIndexed s v (replaceInTypeScheme tySch)
replaceInDataConstr (DataConstrNonIndexed s v types) =
  DataConstrNonIndexed s v (map replaceInType types)

replaceInDef :: Def v a -> Def v a
replaceInDef (Def s i b eqs tySch) =
  Def s i b (replaceInEquations eqs) (replaceInTypeScheme tySch)

replaceInEquations :: EquationList v a -> EquationList v a
replaceInEquations (EquationList s v b eqs) =
  EquationList s v b (map replaceInEquation eqs)

replaceInEquation :: Equation v a -> Equation v a
replaceInEquation (Equation s n a b pats body) =
  Equation s n a b pats (replaceInExpr body)

replaceInExpr :: Expr v a -> Expr v a
replaceInExpr (App s a b e1 e2) =
  App s a b (replaceInExpr e1) (replaceInExpr e2)
replaceInExpr (AppTy s a b e  t) =
  AppTy s a b (replaceInExpr e) (replaceInType t)
replaceInExpr (Binop s a b op e1 e2) =
  Binop s a b op (replaceInExpr e1) (replaceInExpr e2)
replaceInExpr (LetDiamond s a b p mt e1 e2) =
  LetDiamond s a b p (replaceInMaybeType mt) (replaceInExpr e1) (replaceInExpr e2)
replaceInExpr (TryCatch s a b e1 p mt e2 e3) =
  TryCatch s a b (replaceInExpr e1) p (replaceInMaybeType mt) (replaceInExpr e2) (replaceInExpr e3)
replaceInExpr (Val s a b v) = Val s a b v
replaceInExpr (Case s a b e patsAndExprs) =
  Case s a b (replaceInExpr e) (map (\(a, b) -> (a, replaceInExpr b)) patsAndExprs)
replaceInExpr (Hole s a b ids) = Hole s a b ids

replaceInTypeScheme :: TypeScheme -> TypeScheme
replaceInTypeScheme (Forall s quants constraints t) =
  Forall s (map (\(v, t) -> (v, replaceInType t)) quants)
    (map replaceInType constraints)
    (replaceInType t)

replaceInMaybeType :: Maybe Type -> Maybe Type
replaceInMaybeType Nothing = Nothing
replaceInMaybeType (Just t) = Just (replaceInType t)

replaceInType :: Type -> Type
replaceInType =
    runIdentity . typeFoldM (baseTypeFold { tfTyCon = tyCons })
  where
    tyCons id = return $
      case lookup id typeAliases of
        Just t  -> t
        Nothing -> TyCon id


