{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}

{-# options_ghc -fno-warn-incomplete-uni-patterns -Wno-deprecations #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- | Data types in the type checker
module Language.Granule.Checker.DataTypes where

import Data.List (nub)
import Control.Monad.State.Strict


import Language.Granule.Context
import Language.Granule.Checker.Kinding
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Variables (freshIdentifierBase)
import Language.Granule.Checker.Types

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Helpers hiding (freshIdentifierBase)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type hiding (Polarity)

import Language.Granule.Utils

-- Given a data type declaration, register it into the type checker state
-- (including its kind and whether any of its parameters are type indices)
registerTypeConstructor :: DataDecl -> Checker ()
registerTypeConstructor d@(DataDecl sp name tyVars kindAnn ds) =
  modify' $ \st ->
    st { typeConstructors = (name, (tyConKind, dataConstrIds, typeIndicesPositions d)) : typeConstructors st }
  where
    -- the IDs of data constructors
    dataConstrIds = map dataConstrId ds
    -- Calculate the kind for the type constructor
    tyConKind = mkKind tyVars
    mkKind :: Ctxt Type -> Type
    mkKind [] = case kindAnn of Just k -> k; Nothing -> Type 0 -- default to `Type`
    mkKind ((id,v):vs) = FunTy (Just id) Nothing v (mkKind vs)

-- Given a data type decalaration, check and register its data constructors
-- into the scope.
-- __Requires registerTypeConstructor to have been applied first so that the
-- kinds of all data types are known__
registerDataConstructors :: (?globals :: Globals) => DataDecl -> Checker ()
registerDataConstructors d@(DataDecl sp name tyVars k dataConstrs) = do
    -- Retrieve the kind of this type constructor which should already been in scope.
    st <- get
    let kind = case lookup name (typeConstructors st) of
                Just (kind, _ , _) -> kind
                -- Shouldn't happen if `registerTypeConstructor` has already been applied
                _ -> error $ "Internal error. Trying to lookup data constructor " <> pretty name

    -- Split the type variables into those that are paremters, and those that are indices
    let (tyParams, tyIndices) = discriminateTypeIndicesOfDataType d
    -- Check and register each data constructor
    mapM_ (checkDataCon name kind (typeIndices d) tyParams tyIndices) dataConstrs

checkDataCon :: (?globals :: Globals)
  => Id            -- ^ The type constructor and associated type to check against
  -> Kind          -- ^ The kind of the type constructor
  -> [(Id, [Int])] -- ^ Type Indices of this data constructor
  -> [(Id, Kind)]  -- ^ type parameters
  -> [(Id, Kind)]  -- ^ type indices
  -> DataConstr    -- ^ The data constructor to check
  -> Checker ()     -- ^ Return @Just ()@ on success, @Nothing@ on failure
checkDataCon
  tName
  kind
  indices
  tyConParams
  tyConIndices
  d@(DataConstrIndexed sp dName tySch@(Forall s dataConTyVars constraints ty)) =
    case leftmostOfApplication (resultType ty) of
      TyCon tConName | tName == tConName -> do
        -- type variables from the type constructor are the parameters and type indices combined
        let tyConVars = tyConParams ++ tyConIndices

        -- Focus on just those bound variables in scope which are used in the type
        let relevantTyVars = relevantSubCtxt (freeVars ty) (tyConVars <> dataConTyVars)
        reportM ("relevantTyVars = " <> pretty relevantTyVars)

        -- Which variables are bound in this data constructor but don't appear in the result?
        -- These are existentials
        let dataConTyVarsInResultType = relevantSubCtxt (freeVars $ resultType ty) dataConTyVars
        let tyVarsExistials = dataConTyVars `subtractCtxt` dataConTyVarsInResultType

        -- TODO: probably can be removed
        -- if (not (null tyVarsExistials))
        --   then throw $ VariablesNotInResultType s tName (map fst tyVarsExistials)
        --   else do
        -- Add quanitifers to the type variables
        tyVarsForallAndPis <- refineBinderQuantification (relevantTyVars `subtractCtxt` tyVarsExistials) ty

        modify $ \st -> st { tyVarContext =
                tyVarsForallAndPis <> [(v, (k, InstanceQ)) | (v, k) <- tyVarsExistials]}

        -- Check we are making something that is actually a type
        (_, ty) <- checkKind sp ty ktype

        -- type index positions for this data constructor
        let typeIndexPositions = case lookup dName indices of
              Just inds -> inds
              _ -> []

        -- Construct new type scheme for the data constructor
        let dataConTyVarsNew = relevantTyVars -- <> newTyVars
        let tySch = Forall sp dataConTyVarsNew constraints ty

        -- Register this data constructor into the environment
        registerDataConstructor tySch [] typeIndexPositions

      _ ->
        throw $ DataConstructorReturnTypeError s tName (resultType ty)

   where
    -- Given a list (first parameter) of positions explaining which of a list
    -- of kinds (second parameter) are type indices, then output a list
    -- of kinds paired with a boolean where True means it is a type index
    -- -- and False means it is a type parameter
    -- flagTypeIndices :: [Int] -> [Kind] -> [(Bool, Kind)]
    -- flagTypeIndices indexPositions kinds =
    --     flagTypeIndices' indexPositions (zip [0..] kinds)
    --   where
    --     flagTypeIndices' indexPositions [] = []
    --     flagTypeIndices' indexPositions ((n, k):nAndKs) =
    --       (n `elem` indexPositions, k) : flagTypeIndices' indexPositions nAndKs

      registerDataConstructor dataConstrTy coercions indexPositions = do
        st <- get
        case extend (dataConstructors st) dName (dataConstrTy, coercions, indexPositions) of
          Just ds -> put st { dataConstructors = ds }
          Nothing -> throw DataConstructorNameClashError{ errLoc = sp, errId = dName }

checkDataCon tName kind indices tyConParams tyConIndices d@DataConstrNonIndexed{}
  = checkDataCon tName kind indices tyConParams tyConIndices
    $ nonIndexedToIndexedDataConstr tName (tyConParams ++ tyConIndices) d


{-
    Checks whether the type constructor name matches the return constructor
    of the data constructor

    and at the same time generate coercions for every indix of result type constructor
    then generate fresh variables for parameter and coercions that are either trivial
    variable ones or to concrete types

    e.g.
      checkAndGenerateSubstitution Maybe (a' -> Maybe a') [(False, Type)]
      > (a' -> Maybe a', [], [])

      checkAndGenerateSubstitution Other (a' -> Maybe a') [(_, Type)]
      > *** fails

      checkAndGenerateSubstitution Vec (Vec 0 t') [(True, Nat), (False, Type)]
      > (Vec n t', [n |-> 0], [n : Type])

      checkAndGenerateSubstitution Vec (t' -> Vec n' t' -> Vec (n'+1) t') [(True, Nat), (False, Type)]
      > (t' -> Vec n' t' -> Vec n t, [n |-> (n'+1)], [n : Nat])

      checkAndGenerateSubstitution Foo (Int -> Foo Int) [(True, Type)]
      > (Int -> Foo t1, [t1 |-> Int], [t1 : Type])

-}

checkAndGenerateSubstitution ::
       Span                     -- ^ Location of this application
    -> Id                       -- ^ Name of the type constructor
    -> Type                     -- ^ Type of the data constructor
    -> [(Bool, Kind)]           -- ^ Kinds of the (remaining) type constructor parameters
    -> Checker (Type, Substitution, Ctxt Kind)
checkAndGenerateSubstitution sp tName ty ixkinds =
    checkAndGenerateSubstitution' sp tName ty (reverse ixkinds)
  where
    checkAndGenerateSubstitution' sp tName (TyCon tC) []
        | tC == tName = return (TyCon tC, [], [])
        | otherwise = throw UnexpectedTypeConstructor
          { errLoc = sp, tyConActual = tC, tyConExpected = tName }

    -- Recurse through function types, applying this function to the result type
    checkAndGenerateSubstitution' sp tName (FunTy id grade arg res) kinds = do
      (res', subst, tyVarsNew) <- checkAndGenerateSubstitution' sp tName res kinds
      return (FunTy id grade arg res', subst, tyVarsNew)

    checkAndGenerateSubstitution' sp tName (TyApp fun arg) ((True,kind):kinds) = do
      varSymb <- freshIdentifierBase "t"
      let var = mkId varSymb
      (fun', subst, tyVarsNew) <-  checkAndGenerateSubstitution' sp tName fun kinds
      return (TyApp fun' (TyVar var), (var, SubstT arg) : subst, (var, kind) : tyVarsNew)

    checkAndGenerateSubstitution' sp tName (TyApp fun arg) ((False, _):kinds) = do
      (fun', subst, tyVarsNew) <-  checkAndGenerateSubstitution' sp tName fun kinds
      return (TyApp fun' arg, subst, tyVarsNew)

    checkAndGenerateSubstitution' sp _ t _ =
      throw InvalidTypeDefinition { errLoc = sp, errTy = t }


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