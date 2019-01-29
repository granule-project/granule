{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Granule.Syntax.Def where

import Data.List ((\\), delete)
import GHC.Generics (Generic)

import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pattern

-- | Top-level ASTs
-- | Comprise a list of data type declarations and a list
-- | of expression definitions
-- | where `v` is the type of values and `a` annotations
data AST v a = AST [DataDecl] [Def v a] [IFace] [Instance v a]

deriving instance (Show v, Show a) => Show (AST v a)
deriving instance (Eq v, Eq a) => Eq (AST v a)
deriving instance Functor (AST v)

-- | Function definitions
data Def v a = Def Span Id [Equation v a] TypeScheme
  deriving Generic

-- | Single equation of a function
data Equation v a =
    Equation Span a [Pattern a] (Expr v a)
  deriving Generic

deriving instance Functor (Def v)
deriving instance Functor (Equation v)
deriving instance (Show v, Show a) => Show (Def v a)
deriving instance (Eq v, Eq a) => Eq (Def v a)
deriving instance (Show v, Show a) => Show (Equation v a)
deriving instance (Eq v, Eq a) => Eq (Equation v a)

instance FirstParameter (Def v a) Span
instance FirstParameter (Equation v a) Span

-- | Data type declarations
data DataDecl = DataDecl Span Id [(Id,Kind)] (Maybe Kind) [DataConstr]
  deriving (Generic, Show, Eq)

instance FirstParameter DataDecl Span

-- | Data constructors
data DataConstr
  = DataConstrG Span Id TypeScheme -- ^ GADTs
  | DataConstrA Span Id [Type]     -- ^ ADTs
  deriving (Eq, Show, Generic)

instance FirstParameter DataConstr Span

-- | How many data constructors a type has (Nothing -> don't know)
type Cardinality = Maybe Nat


-- | Interfaces
data IFace =
  IFace
  Span
  Id           -- ^ interface name
  [IConstr]    -- ^ constraints
  (Maybe Kind) -- ^ kind of parameter
  Id           -- ^ name of parameter
  [IFaceTy]
  deriving (Show, Eq)


-- | Interface types
data IFaceTy = IFaceTy Span Id TypeScheme
  deriving (Generic, Show, Eq)

instance FirstParameter IFaceTy Span


-- | Instances
data Instance v a =
  Instance
  Span
  Id         -- ^ interface name
  [IConstr]  -- ^ constraints
  IFaceDat   -- ^ instance type
  [IDef v a] -- ^ implementations

deriving instance Functor (Instance v)
deriving instance (Eq v, Eq a) => Eq (Instance v a)
deriving instance (Show v, Show a) => Show (Instance v a)

-- | Instance implementation
data IDef v a = IDef Span (Maybe String) (Equation v a)
  deriving (Generic)

instance FirstParameter (IDef v a) Span
deriving instance Functor (IDef v)
deriving instance (Eq v, Eq a) => Eq (IDef v a)
deriving instance (Show v, Show a) => Show (IDef v a)


-- | Instance type
data IFaceDat = IFaceDat Span Id [Type]
  deriving (Show, Generic, Eq)

instance FirstParameter IFaceDat Span


-- | Fresh a whole AST
freshenAST :: AST v a -> AST v a
freshenAST (AST dds defs ifaces insts) =
  AST dds' defs' ifaces insts
    where (dds', defs') = (map runFreshener dds, map runFreshener defs)

instance Monad m => Freshenable m DataDecl where
  freshen (DataDecl s v tyVars kind ds) = do
    tyVars <- mapM (\(v, k) -> freshen k >>= \k' -> return (v, k')) tyVars
    kind <- freshen kind
    ds <- freshen ds
    return $ DataDecl s v tyVars kind ds

instance Monad m => Freshenable m DataConstr where
  freshen (DataConstrG sp v tys) = do
    tys <- freshen tys
    return $ DataConstrG sp v tys
  freshen (DataConstrA sp v ts) = do
    ts <- mapM freshen ts
    return $ DataConstrA sp v ts

instance Monad m => Freshenable m (Equation v a) where
  freshen (Equation s a ps e) = do
    ps <- mapM freshen ps
    e <- freshen e
    return (Equation s a ps e)

-- | Alpha-convert all bound variables of a definition to unique names.
instance Monad m => Freshenable m (Def v a) where
  freshen (Def s var eqs t) = do
    t  <- freshen t
    eqs <- mapM freshen eqs
    return (Def s var eqs t)

instance Term (Equation v a) where
  freeVars (Equation s a binders body) =
      freeVars body \\ concatMap boundVars binders

instance Term (Def v a) where
  freeVars (Def _ name equations _) =
    delete name (concatMap freeVars equations)
