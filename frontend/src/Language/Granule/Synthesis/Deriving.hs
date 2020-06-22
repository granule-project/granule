module Language.Granule.Synthesis.Deriving
  (derivePush, derivePull) where

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Span
import Language.Granule.Context

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Variables
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Synthesis.Builders

import Language.Granule.Utils

  {-
  Module for automatically deriving graded linear logical
  operations based on types.
  -}

derivePush :: (?globals :: Globals) => Type -> Checker (TypeScheme, Def () Type)
derivePush ty = do
  -- Derive
  (tyS, expr) <- derivePush' [] ty
  -- Build derived expression into definition wrapper
  let name = mkId $ "push" ++ pretty ty
  return $
    (tyS, Def nullSpanNoFile name True
            (EquationList nullSpanNoFile name True
               [Equation nullSpanNoFile name (unforall tyS) True [] expr]) tyS)

derivePush' :: Ctxt Id -> Type -> Checker (TypeScheme, Expr () Type)

-- Unit case:  push @() = (\x -> case x of () -> ()) : () -> ()
derivePush' _sigma (TyCon (internalName -> "()")) = do
  x <- freshIdentifierBase "x" >>= (return . mkId)
  let tyScheme = trivialScheme (FunTy Nothing (TyCon $ mkId "()") (TyCon $ mkId "()"))
  return (tyScheme, makeAbs x (makeUnitElim x makeUnitIntro (trivialScheme (TyCon $ mkId "()"))) tyScheme)

derivePush' _ _ = do
  error "Cannot derive"

derivePull :: Ctxt (Ctxt (TypeScheme, Substitution)) -> Type -> (TypeScheme, Def () ())
derivePull = error "stub"