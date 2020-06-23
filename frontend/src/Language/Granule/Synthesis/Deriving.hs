module Language.Granule.Synthesis.Deriving
  (derivePush, derivePull) where

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Span
import Language.Granule.Context

--import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Variables
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Synthesis.Builders

import Language.Granule.Utils

  {-
  Module for automatically deriving graded linear logical
  operations based on types.
  -}

pbox :: Coeffect -> Type -> Pattern Type -> Pattern Type
pbox c t = PBox nullSpanNoFile (Box c t) True

derivePush :: (?globals :: Globals) => Type -> Checker (TypeScheme, Def () Type)
derivePush ty = do
  -- Create fresh variables for the grades
  kVar <- freshIdentifierBase "k" >>= (return . mkId)
  cVar <- freshIdentifierBase "r" >>= (return . mkId)

  -- Derive
  -- kind <- inferKindOfType nullSpanNoFile ty
  (funTy, expr) <- derivePush' (CVar cVar) [] ty

  -- Build derived type scheme and definition wrapper
  let tyS = Forall nullSpanNoFile
              [(kVar, KCoeffect), (cVar, KPromote (TyVar kVar))]
              []
              funTy
  let name = mkId $ "push" ++ pretty ty
  return $
    (tyS, Def nullSpanNoFile name True
            (EquationList nullSpanNoFile name True
               [Equation nullSpanNoFile name (unforall tyS) True [] expr]) tyS)

derivePush' :: Coeffect -> Ctxt Id -> Type -> Checker (Type, Expr () Type)

-- Unit case:  push @() = (\x -> case x of () -> ()) : () -> ()
derivePush' c _sigma argTy@(TyCon (internalName -> "()")) = do
  x <- freshIdentifierBase "x" >>= (return . mkId)
  let ty  = FunTy Nothing (Box c argTy) argTy
  let tyS = trivialScheme ty
  return (ty, makeAbs x (makeUnitElimP (pbox c argTy) x makeUnitIntro (trivialScheme argTy)) tyS)

{-
derivePush' _sigma (isProduct -> Just (t1, t2)) = do
  derivePush' _sigma t1
  derivePush' _sigma t2

-}

derivePush' _ _ _ = do
  error "Cannot derive"

derivePull :: Ctxt (Ctxt (TypeScheme, Substitution)) -> Type -> (TypeScheme, Def () ())
derivePull = error "stub"