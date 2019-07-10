{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

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
    SubstT  Type
  | SubstC  Coeffect
  | SubstK  Kind
  | SubstE  Effect
  deriving (Eq, Show)

instance Pretty Substitutors where
  prettyL l (SubstT t) = prettyL l t
  prettyL l (SubstC c) = prettyL l c
  prettyL l (SubstK k) = prettyL l k
  prettyL l (SubstE e) = prettyL l e

instance Term Substitution where
  freeVars [] = []
  freeVars ((v, SubstT t):subst) =
    freeVars t ++ freeVars subst
  freeVars ((v, SubstC c):subst) =
    freeVars c ++ freeVars subst
  freeVars ((v, SubstK k):subst) =
    freeVars k ++ freeVars subst
  freeVars ((v, SubstE e):subst) =
    -- freeVars e ++
    -- TODO: when effects become terms we can do something here
    freeVars subst


-- | For substitutions which are just renaminings
--   allow the substitution to be inverted
flipSubstitution :: Substitution -> Substitution
flipSubstitution [] = []
flipSubstitution ((var, SubstT (TyVar var')):subst) =
    (var', SubstT (TyVar var)) : flipSubstitution subst

-- Can't flip the substitution so ignore it
flipSubstitution (s:subst) = flipSubstitution subst
