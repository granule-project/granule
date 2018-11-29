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
deriving instance (Show (Def v a), Show a) => Show (AST v a)
deriving instance (Eq (Def v a), Eq a) => Eq (AST v a)

-- | Function definitions
data Def v a = Def Span Id [Equation v a] TypeScheme
  deriving Generic
deriving instance (Show v, Show a) => Show (Def v a)
deriving instance (Eq v, Eq a) => Eq (Def v a)

-- | Single equation of a function
data Equation v a =
    Equation Span a [Pattern a] (Expr v a)
  deriving Generic
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
  = DataConstrIndexed Span Id TypeScheme -- ^ GADTs
  | DataConstrNonIndexed Span Id [Type]  -- ^ ADTs
  deriving (Eq, Show, Generic)

nonIndexedToIndexedDataConstr :: Id -> [(Id, Kind)] -> DataConstr -> DataConstr
nonIndexedToIndexedDataConstr _     _      d@DataConstrIndexed{} = d
nonIndexedToIndexedDataConstr tName tyVars (DataConstrNonIndexed sp dName params)
    -- Don't push the parameters into the type scheme yet
    = DataConstrIndexed sp dName (Forall sp [] [] ty)
  where
    ty = foldr FunTy (returnTy (TyCon tName) tyVars) params
    returnTy t [] = t
    returnTy t (v:vs) = returnTy (TyApp t ((TyVar . fst) v)) vs

instance FirstParameter DataConstr Span

-- | How many data constructors a type has (Nothing -> don't know)
type Cardinality = Maybe Nat


-- | Interfaces
data IFace = IFace deriving (Show, Eq)


-- | Instances
data Instance v a = Instance deriving (Show)

deriving instance Functor (Instance v)
deriving instance (Eq v, Eq a) => Eq (Instance v a)


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
  freshen (DataConstrIndexed sp v tys) = do
    tys <- freshen tys
    return $ DataConstrIndexed sp v tys
  freshen (DataConstrNonIndexed sp v ts) = do
    ts <- mapM freshen ts
    return $ DataConstrNonIndexed sp v ts

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
