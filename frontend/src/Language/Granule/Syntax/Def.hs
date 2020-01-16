{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Granule.Syntax.Def where

import Data.List ((\\), delete)
import Data.Set (Set)
import qualified Data.Map as M
import GHC.Generics (Generic)

import Language.Granule.Context (Ctxt)
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
data AST v a =
  AST
    { dataTypes :: [DataDecl]
    , definitions :: [Def v a]
    , imports :: Set Import
    , hiddenNames :: M.Map Id Id -- map from names to the module hiding them
    , moduleName  :: Maybe Id
    }
deriving instance (Show (Def v a), Show a) => Show (AST v a)
deriving instance (Eq (Def v a), Eq a) => Eq (AST v a)

type Import = FilePath

-- | Function definitions
data Def v a = Def
  { defSpan :: Span
  , defId :: Id
  , defEquations :: [Equation v a]
  , defTypeScheme :: TypeScheme
  }
  deriving Generic

deriving instance (Eq v, Eq a) => Eq (Def v a)
deriving instance (Show v, Show a) => Show (Def v a)

-- | Single equation of a function
data Equation v a =
    Equation {
        equationSpan       :: Span,
        equationAnnotation :: a,
        equationPatterns   :: [Pattern a],
        equationBody       :: Expr v a }
    deriving Generic

deriving instance (Eq v, Eq a) => Eq (Equation v a)
deriving instance (Show v, Show a) => Show (Equation v a)
instance FirstParameter (Equation v a) Span

definitionType :: Def v a -> Type
definitionType Def { defTypeScheme = ts } =
    ty where (Forall _ _ _ ty) = ts

-- | Data type declarations
data DataDecl = DataDecl
  { dataDeclSpan :: Span
  , dataDeclId :: Id
  , dataDeclTyVarCtxt :: Ctxt Kind
  , dataDeclKindAnn :: Maybe Kind
  , dataDeclDataConstrs :: [DataConstr]
  }
  deriving (Generic, Show, Eq)

instance FirstParameter DataDecl Span

-- | Data constructors
data DataConstr
  = DataConstrIndexed
    { dataConstrSpan :: Span, dataConstrId :: Id, dataConstrTypeScheme :: TypeScheme } -- ^ GADTs
  | DataConstrNonIndexed
    { dataConstrSpan :: Span, dataConstrId :: Id, dataConstrParams :: [Type] } -- ^ ADTs
  deriving (Eq, Show, Generic)

-- | Is the data type an indexed data type, or just a plain ADT?
isIndexedDataType :: DataDecl -> Bool
isIndexedDataType (DataDecl _ id tyVars _ constrs) =
    all nonIndexedConstructors constrs
  where
    nonIndexedConstructors DataConstrNonIndexed{} = False
    nonIndexedConstructors (DataConstrIndexed _ _ (Forall _ tyVars' _ ty)) =
      noMatchOnEndType (reverse tyVars) ty

    noMatchOnEndType ((v, _):tyVars) (TyApp t1 t2) =
      case t2 of
        TyVar v' | v == v' -> noMatchOnEndType tyVars t1
        _                  -> True
    noMatchOnEndType tyVars (FunTy _ _ t) = noMatchOnEndType tyVars t
    noMatchOnEndType [] (TyCon _) = False
    -- Defaults to `true` (acutally an ill-formed case for data types)
    noMatchOnEndType _ _ = True


nonIndexedToIndexedDataConstr :: Id -> [(Id, Kind)] -> DataConstr -> DataConstr
nonIndexedToIndexedDataConstr _     _      d@DataConstrIndexed{} = d
nonIndexedToIndexedDataConstr tName tyVars (DataConstrNonIndexed sp dName params)
    -- Don't push the parameters into the type scheme yet
    = DataConstrIndexed sp dName (Forall sp [] [] ty)
  where
    ty = foldr (FunTy Nothing) (returnTy (TyCon tName) tyVars) params
    returnTy t [] = t
    returnTy t (v:vs) = returnTy (TyApp t ((TyVar . fst) v)) vs

instance FirstParameter DataConstr Span

-- | How many data constructors a type has (Nothing -> don't know)
type Cardinality = Maybe Nat

-- | Fresh a whole AST
freshenAST :: AST v a -> AST v a
freshenAST (AST dds defs imports hiddens name) =
  AST dds' defs' imports hiddens name
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
