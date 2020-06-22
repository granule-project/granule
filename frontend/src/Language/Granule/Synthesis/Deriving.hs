module Language.Granule.Synthesis.Deriving
  (derivePush, derivePull) where

import Language.Granule.Syntax.Type
-- import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Def
import Language.Granule.Context
import Language.Granule.Checker.SubstitutionContexts

  {-
  Module for automatically deriving graded linear logical
  operations based on types.
  -}

derivePush :: Ctxt (Ctxt (TypeScheme, Substitution)) -> Type -> (TypeScheme, Def () ())
derivePush = error "stub"

derivePull :: Ctxt (Ctxt (TypeScheme, Substitution)) -> Type -> (TypeScheme, Def () ())
derivePull = error "stub"