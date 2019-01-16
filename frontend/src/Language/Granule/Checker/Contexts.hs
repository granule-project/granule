{-# LANGUAGE FlexibleInstances #-}

module Language.Granule.Checker.Contexts where

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pretty

-- | Assumptions
data Assumption =
    Linear Type
  | Discharged Type Coeffect
    deriving (Eq, Show)

-- | Assumptions of top-level things with type scheme
data TysAssumption =
    Unrestricted TypeScheme
  | Restricted TypeScheme Coeffect
    deriving (Eq, Show)

assumptionTypeScheme :: TysAssumption -> TypeScheme
assumptionTypeScheme (Unrestricted t) = t
assumptionTypeScheme (Restricted t _) = t

toDefAssumption :: Maybe Coeffect -> TypeScheme -> TysAssumption
toDefAssumption Nothing t = Unrestricted t
toDefAssumption (Just c) t = Restricted t c

instance Pretty TysAssumption where
    prettyL l (Unrestricted ty) = prettyL l ty
    prettyL l (Restricted t c) = ".[" <> prettyL l t <> "]. " <> prettyL l c

instance Pretty Assumption where
    prettyL l (Linear ty) = prettyL l ty
    prettyL l (Discharged t c) = ".[" <> prettyL l t <> "]. " <> prettyL l c

instance {-# OVERLAPS #-} Pretty (Id, Assumption) where
   prettyL l (a, b) = prettyL l a <> " : " <> prettyL l b
