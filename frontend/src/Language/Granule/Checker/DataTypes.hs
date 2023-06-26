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

-- | Core type checker
module Language.Granule.Checker.DataTypes where

import Control.Monad.State.Strict

import Language.Granule.Checker.Monad

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Type hiding (Polarity)


-- Given a data type declaration
-- check t
registerTypeConstructor :: DataDecl -> Checker ()
registerTypeConstructor d@(DataDecl sp name tyVars kindAnn ds) = 
  modify' $ \st ->
    st { typeConstructors = (name, (tyConKind, dataConstrIds, typeIndicesPositions d)) : typeConstructors st }
  where
    -- the IDs of data constructors
    dataConstrIds = map dataConstrId ds 
    -- Calculate the kind for the type constructor
    tyConKind = mkKind (map snd tyVars)
    mkKind [] = case kindAnn of Just k -> k; Nothing -> Type 0 -- default to `Type`
    mkKind (v:vs) = FunTy Nothing v (mkKind vs)
