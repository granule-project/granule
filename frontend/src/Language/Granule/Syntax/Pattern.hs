{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Language.Granule.Syntax.Pattern where

import GHC.Generics (Generic)
import qualified Text.Reprinter as Rp

import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.Annotated
import Language.Granule.Syntax.SecondParameter
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span

-- | Language.Granule.Syntax of patterns
data Pattern a
  = PVar Span a Bool Id                -- ^ Variable patterns
  | PWild Span a Bool                  -- ^ Wildcard (underscore) pattern
  | PBox Span a Bool (Pattern a)       -- ^ Box patterns
  | PInt Span a Bool Int               -- ^ Numeric patterns
  | PFloat Span a Bool Double          -- ^ Float pattern
  | PConstr Span a Bool Id [Pattern a] -- ^ Constructor pattern
  deriving (Eq, Show, Generic, Functor, Rp.Data)

instance Term (Pattern a) where
  freeVars _ = []
  hasHole _ = False

  isLexicallyAtomic (PConstr _ _ _ _ pats) = null pats
  isLexicallyAtomic _  = True

-- | First parameter of patterns is their span
instance FirstParameter (Pattern a) Span
instance SecondParameter (Pattern a) a

instance Annotated (Pattern a) a where
    annotation = getSecondParameter

patternFold
  :: (Span -> ann -> Bool -> Id -> b)
  -> (Span -> ann -> Bool -> b)
  -> (Span -> ann -> Bool -> b -> b)
  -> (Span -> ann -> Bool -> Int -> b)
  -> (Span -> ann -> Bool -> Double -> b)
  -> (Span -> ann -> Bool -> Id -> [b] -> b)
  -> Pattern ann
  -> b
patternFold v w b i f c = go
  where
    go = \case
      PVar sp ann rf nm -> v sp ann rf nm
      PWild sp ann rf  -> w sp ann rf
      PBox sp ann rf pat -> b sp ann rf (go pat)
      PInt sp ann rf int -> i sp ann rf int
      PFloat sp ann rf doub -> f sp ann rf doub
      PConstr sp ann rf nm pats -> c sp ann rf nm (go <$> pats)

patternFoldM
  :: (Monad m)
  => (Span -> ann -> Bool -> Id -> m b)
  -> (Span -> ann -> Bool -> m b)
  -> (Span -> ann -> Bool -> b -> m b)
  -> (Span -> ann -> Bool -> Int -> m b)
  -> (Span -> ann -> Bool -> Double -> m b)
  -> (Span -> ann -> Bool -> Id -> [b] -> m b)
  -> Pattern ann
  -> m b
patternFoldM v w b i f c = go
  where
    go = \case
      PVar sp ann rf nm -> v sp ann rf nm
      PWild sp ann rf -> w sp ann rf
      PBox sp ann rf pat ->
        do
            pat' <- go pat
            b sp ann rf pat'
      PInt sp ann rf int -> i sp ann rf int
      PFloat sp ann rf doub -> f sp ann rf doub
      PConstr sp ann rf nm pats ->
        do
            pats' <- mapM go pats
            c sp ann rf nm pats'

-- | Variables bound by patterns
boundVars :: Pattern a -> [Id]
boundVars (PVar _ _ _ v)     = [v]
boundVars PWild {}       = []
boundVars (PBox _ _ _ p)     = boundVars p
boundVars PInt {}        = []
boundVars PFloat {}      = []
boundVars (PConstr _ _ _ _ ps) = concatMap boundVars ps

boundVarsAndAnnotations :: Pattern a -> [(a, Id)]
boundVarsAndAnnotations =
    patternFold var wild box int flt cstr
    where var _ ty _ ident  = [(ty, ident)]
          wild _ _ _        = []
          box _ _ _ pat     = pat
          int _ _ _ _       = []
          flt _ _ _ _       = []
          cstr _ _ _ _ pats = concat pats

ppair :: Span
      -> a
      -> Pattern a
      -> Pattern a
      -> Pattern a
ppair s annotation left right =
    PConstr s annotation False (mkId "(,)") [left, right]

-- >>> runFreshener (PVar ((0,0),(0,0)) (Id "x" "x"))
-- PVar ((0,0),(0,0)) (Id "x" "x_0")

-- | Freshening for patterns
instance Freshenable m (Pattern a) where

  freshen :: Monad m => Pattern a -> Freshener m (Pattern a)
  freshen (PVar s a rf var) = do
      var' <- freshIdentifierBase Value var
      return $ PVar s a rf var'

  freshen (PBox s a rf p) = do
      p' <- freshen p
      return $ PBox s a rf p'

  freshen (PConstr s a rf name ps) = do
      ps <- mapM freshen ps
      return (PConstr s a rf name ps)

  freshen p@PWild {} = return p
  freshen p@PInt {} = return p
  freshen p@PFloat {} = return p
