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

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Type


-- | Rewrite a type-annotated AST to an intermediate
-- | representation without interfaces.
rewriteWithoutInterfaces :: AST v Type -> AST v ()
rewriteWithoutInterfaces (AST dds defs _ _) = forgetAnnotations $ AST dds defs [] []


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
