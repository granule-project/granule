module Language.Granule.Checker.SubstitutionContexts where

import Language.Granule.Context
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pretty

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
  prettyL l (SubstT t) = "->" <> prettyL l t
  prettyL l (SubstC c) = "->" <> prettyL l c
  prettyL l (SubstK k) = "->" <> prettyL l k
  prettyL l (SubstE e) = "->" <> prettyL l e
