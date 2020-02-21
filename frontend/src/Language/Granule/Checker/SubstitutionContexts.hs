{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}

module Language.Granule.Checker.SubstitutionContexts where

import Language.Granule.Context
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Helpers

{-| Substitutions map from variables to type-level things as defined by
    substitutors -}
type Substitution = Ctxt Substitutors

{-| Substitutors are things we want to substitute in... they may be one
     of several things... -}
data Substitutors =
    SubstT  (Type Zero)
  | SubstC  Coeffect
  | SubstK  Kind
  deriving (Eq, Show)

instance Pretty Substitutors where
  pretty (SubstT t) = pretty t
  pretty (SubstC c) = pretty c
  pretty (SubstK k) = pretty k

instance Term Substitution where
  freeVars [] = []
  freeVars ((v, SubstT t):subst) =
    freeVars t ++ freeVars subst
  freeVars ((v, SubstC c):subst) =
    freeVars c ++ freeVars subst
  freeVars ((v, SubstK k):subst) =
    freeVars k ++ freeVars subst

-- | For substitutions which are just renaminings
--   allow the substitution to be inverted
flipSubstitution :: Substitution -> Substitution
flipSubstitution [] = []
flipSubstitution ((var, SubstT (TyVar var')):subst) =
    (var', SubstT (TyVar var)) : flipSubstitution subst

-- Can't flip the substitution so ignore it
flipSubstitution (s:subst) = flipSubstitution subst
