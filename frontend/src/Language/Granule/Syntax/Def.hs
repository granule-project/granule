{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}

module Language.Granule.Syntax.Def where

import Data.List ((\\), delete, nub)
import Data.Set (Set)
import qualified Data.Map as M
import GHC.Generics (Generic)
import Data.Data
import qualified Text.Reprinter as Rp

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

extendASTWith :: [Def v a] -> AST v a -> AST v a
extendASTWith defs ast = ast { definitions = defs ++ definitions ast }

deriving instance (Show (Def v a), Show a) => Show (AST v a)
deriving instance (Eq (Def v a), Eq a) => Eq (AST v a)
deriving instance (Data (ExprFix2 ValueF ExprF v a), Data v, Data a) => Data (AST v a)

type Import = FilePath

-- | Function definitions
data Def v a = Def
  { defSpan :: Span
  , defId :: Id
  , defRefactored :: Bool
  , defEquations :: EquationList v a
  , defTypeScheme :: TypeScheme
  }
  deriving (Generic)

deriving instance (Eq v, Eq a) => Eq (Def v a)
deriving instance (Show v, Show a) => Show (Def v a)
deriving instance (Data (ExprFix2 ValueF ExprF v a), Data v, Data a) => Data (Def v a)

instance Rp.Refactorable (Def v a) where
  isRefactored def = if defRefactored def then Just Rp.Replace else Nothing

  getSpan = convSpan . defSpan

-- | A list of equations
data EquationList v a = EquationList
  { equationsSpan :: Span
  , equationsId :: Id
  , equationsRefactored :: Bool
  , equations :: [Equation v a]
  } deriving (Generic)

deriving instance (Eq v, Eq a) => Eq (EquationList v a)
deriving instance (Show v, Show a) => Show (EquationList v a)
deriving instance (Data (ExprFix2 ValueF ExprF v a), Data v, Data a) => Data (EquationList v a)
instance FirstParameter (EquationList v a) Span

instance Rp.Refactorable (EquationList v a) where
  isRefactored eqnList = if equationsRefactored eqnList then Just Rp.Replace else Nothing

  getSpan = convSpan . equationsSpan

consEquation :: Equation v a -> EquationList v a -> EquationList v a
consEquation eqn EquationList{..} =
  let newStartPos = startPos (equationSpan eqn)
      newSpan = equationsSpan { startPos = newStartPos }
  in EquationList newSpan equationsId equationsRefactored (eqn : equations)

-- | Single equation of a function
data Equation v a =
    Equation {
        equationSpan       :: Span,
        equationId         :: Id,
        equationAnnotation :: a,
        equationRefactored :: Bool,
        equationPatterns   :: [Pattern a],
        equationBody       :: Expr v a }
    deriving (Generic)

deriving instance (Eq v, Eq a) => Eq (Equation v a)
deriving instance (Show v, Show a) => Show (Equation v a)
deriving instance (Data (ExprFix2 ValueF ExprF v a), Data v, Data a) => Data (Equation v a)
instance FirstParameter (Equation v a) Span

instance Rp.Refactorable (Equation v a) where
  isRefactored eqn = if equationRefactored eqn then Just Rp.Replace else Nothing

  getSpan = convSpan . equationSpan

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
  deriving (Generic, Show, Eq, Data)

instance FirstParameter DataDecl Span

-- | Data constructors
data DataConstr
  = DataConstrIndexed
    { dataConstrSpan :: Span, dataConstrId :: Id, dataConstrTypeScheme :: TypeScheme } -- ^ GADTs
  | DataConstrNonIndexed
    { dataConstrSpan :: Span, dataConstrId :: Id, dataConstrParams :: [Type] } -- ^ ADTs
  deriving (Eq, Show, Generic, Typeable, Data)



-- | Is the data type an indexed data type, or just a plain ADT?
isIndexedDataType :: DataDecl -> Bool
isIndexedDataType d = not ((concatMap snd (typeIndices d)) == [])

-- | This returns a list of which parameters are actually indices
-- | If this is not an indexed type this list will be empty.
typeIndicesPositions :: DataDecl -> [Int]
typeIndicesPositions d = nub (concatMap snd (typeIndices d))

-- | Given a data decleration, return the type parameters which are type indicies
typeIndices :: DataDecl -> [(Id, [Int])]
typeIndices (DataDecl _ _ tyVars _ constrs) = 
    map constructorIndices constrs 
  where 
    constructorIndices :: DataConstr -> (Id, [Int])
    constructorIndices dataConstr@(DataConstrNonIndexed _ id _) = (id, [])
    constructorIndices dataConstr@(DataConstrIndexed _ id (Forall _ _ _ ty)) = (id, findIndices 0 (reverse tyVars) ty) 

    findIndices :: Int -> Ctxt Kind -> Type -> [Int]  
    findIndices index ((v, _):tyVars) (TyApp t1 t2) =
      case t2 of
        TyVar v' | v == v' -> findIndices (index+1) tyVars t1
        _                  -> index : findIndices (index+1) tyVars t1
    findIndices index tyVars (FunTy _ _ _ t) = findIndices (index+1) tyVars t
    findIndices _ [] (TyCon _) = []
    -- Defaults to `empty` (acutally an ill-formed case for data types)
    findIndices _ _ _ = []

{-| discriminateTypeIndicesOfDataType takes a data type definition, which has 0 or more
   type parameters, and splits those type parameters into two lists: the first being
   those which are really parameters (in a parametric polymorphism sense), and the second
   which are indices (in the GADT/indexed families sense) -}
discriminateTypeIndicesOfDataType :: DataDecl -> ([(Id, Kind)], [(Id, Kind)])
discriminateTypeIndicesOfDataType d@(DataDecl _ _ tyVars _ _) =
   classify (zip tyVars [0..(length tyVars)])
  where
    -- Partition the variables into two depending on whether
    -- their position makes them an index or not
    classify [] = ([], [])
    classify ((vark, pos) : is) =
      let (params, indices) = classify is
      in
        if pos `elem` typeIndexPositions
        then (params, vark : indices)
        else (vark : params, indices)

    typeIndexPositions = nub $ concatMap snd (typeIndices d)

nonIndexedToIndexedDataConstr :: Id -> [(Id, Kind)] -> DataConstr -> DataConstr
nonIndexedToIndexedDataConstr _     _      d@DataConstrIndexed{} = d
nonIndexedToIndexedDataConstr tName tyVars (DataConstrNonIndexed sp dName params)
    -- Don't push the parameters into the type scheme yet
    = DataConstrIndexed sp dName (Forall sp [] [] ty)
  where
    ty = foldr (FunTy Nothing Nothing) (returnTy (TyCon tName) tyVars) params
    returnTy t [] = t
    returnTy t (v:vs) = returnTy (TyApp t ((TyVar . fst) v)) vs

instance FirstParameter DataConstr Span

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
    return (DataDecl s v tyVars kind ds)

instance Monad m => Freshenable m DataConstr where
  freshen (DataConstrIndexed sp v tys) = do
    tys <- freshen tys
    return $ DataConstrIndexed sp v tys
  freshen (DataConstrNonIndexed sp v ts) = do
    ts <- mapM freshen ts
    return $ DataConstrNonIndexed sp v ts

instance Monad m => Freshenable m (Equation v a) where
  freshen (Equation s name a rf ps e) = do
    ps <- mapM freshen ps
    e <- freshen e
    return (Equation s name a rf ps e)

instance Monad m => Freshenable m (EquationList v a) where
  freshen (EquationList s name rf eqs) = do
    eqs' <- mapM freshen eqs
    return (EquationList s name rf eqs')

-- | Alpha-convert all bound variables of a definition to unique names.
instance Monad m => Freshenable m (Def v a) where
  freshen (Def s var rf eqs t) = do
    t  <- freshen t
    equations' <- mapM freshen (equations eqs)
    let eqs' = eqs { equations = equations' }
    return (Def s var rf eqs' t)

instance Term (EquationList v a) where
  freeVars (EquationList _ name _ eqs) =
    delete name (concatMap freeVars eqs)

instance Term (Equation v a) where
  freeVars (Equation s _ a _ binders body) =
      freeVars body \\ concatMap boundVars binders

instance Term (Def v a) where
  freeVars (Def _ name _ equations _) =
    delete name (freeVars equations)
