{- |
Module      :  Language.Granule.Checker.Instance
Description :  Helpers for working with instances.

This module provides a simplified representation for instances,
designed for the type-safe use and manipulation of instance
information.

The 'Inst' datatype serves a dual purpose:

  - it represents concrete instances (i.e., those defined by the user)
  - it represents interface context and constraints

Thus the instance @Eq A@ could equally be used to indicate that we have
generated a constraint @Eq A@ that needs to be solved, or the user has
defined an instance for @Eq A@ directly.
-}


{-# LANGUAGE ImplicitParams #-}
module Language.Granule.Checker.Instance
    ( Inst
    , mkInst

    -- ** Retrieving information from instances
    , instIFace
    , instParams

    -- ** Simple instance tests
    , isFullyPolymorphicInstance

    -- ** Converting to/from types/instances
    , tyFromInst
    , instFromTy

    -- ** Partitioning constraints
    , partitionConstraints
    ) where


import Data.Either (partitionEithers)
import Data.List (foldl')

import Language.Granule.Syntax.Helpers (Term, freeVars)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type


--------------------------------
----- Simplified Instances -----
--------------------------------


-- | Simplified representation of instances for ease of use.
data Inst = Inst {
    -- | The interface name of an instance.
    instIFace :: Id
  , instParams :: [Type]
  } deriving (Eq, Ord, Show)


instance Pretty Inst where
  prettyL l inst =
      fmap (prettyL l) unwords $ prettyL l (instIFace inst)
           : fmap (prettyL l) (instParams inst)


instance Term Inst where
  freeVars = concatMap freeVars . instParams


-- | Helper for building types that represent
-- | interface applications (i.e., instances).
mkInst :: Id -> [Type] -> Inst
mkInst iname ptys = Inst iname ptys


isFullyPolymorphicInstance :: Inst -> Bool
isFullyPolymorphicInstance = all isTyVar . instParams
  where isTyVar (TyVar _) = True
        isTyVar _ = False


-- | Convert an instance into its type representation.
tyFromInst :: Inst -> Type
tyFromInst inst = foldl' TyApp (TyCon (instIFace inst)) (instParams inst)


-- | Attempt to extract an instance from a type.
-- |
-- | Note that this does not check whether a valid
-- | interface exists, only that the type conforms
-- | to a general instance type.
instFromTy :: Type -> Maybe Inst
instFromTy t = do
  iname <- retCon t
  params <- fmap reverse $ apTys t
  pure $ mkInst iname params
  where retCon (TyCon n) = pure n
        retCon (TyApp c _) = retCon c
        retCon _ = Nothing
        apTys (TyApp (TyCon _) t) = pure $ pure t
        apTys (TyApp x t) = fmap (t:) $ apTys x
        apTys _ = Nothing


-- | Partition a list of constraints into predicates and
-- | interface constraints.
partitionConstraints :: [TConstraint] -> ([Type], [Inst])
partitionConstraints = partitionEithers . fmap (\t -> maybe (Left t) Right $ instFromTy t)
