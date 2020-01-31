{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Language.Granule.Syntax.Pattern where

import GHC.Generics (Generic)

import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.Annotated
import Language.Granule.Syntax.SecondParameter
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span

-- | Language.Granule.Syntax of patterns
data Pattern a
  = PVar Span a Id                -- ^ Variable patterns
  | PWild Span a                  -- ^ Wildcard (underscore) pattern
  | PBox Span a (Pattern a)       -- ^ Box patterns
  | PInt Span a Int               -- ^ Numeric patterns
  | PFloat Span a Double          -- ^ Float pattern
  | PConstr Span a Id [Pattern a] -- ^ Constructor pattern
  deriving (Eq, Show, Generic, Functor)

instance Term (Pattern a) where
  freeVars _ = []
  hasHole _ = False

  isLexicallyAtomic PConstr{} = False
  isLexicallyAtomic _  = True

-- | First parameter of patterns is their span
instance FirstParameter (Pattern a) Span
instance SecondParameter (Pattern a) a

instance Annotated (Pattern a) a where
    annotation = getSecondParameter

patternFold
  :: (Span -> ann -> Id -> b)
  -> (Span -> ann -> b)
  -> (Span -> ann -> b -> b)
  -> (Span -> ann -> Int -> b)
  -> (Span -> ann -> Double -> b)
  -> (Span -> ann -> Id -> [b] -> b)
  -> Pattern ann
  -> b
patternFold v w b i f c = go
  where
    go = \case
      PVar sp ann nm -> v sp ann nm
      PWild sp ann -> w sp ann
      PBox sp ann pat -> b sp ann (go pat)
      PInt sp ann int -> i sp ann int
      PFloat sp ann doub -> f sp ann doub
      PConstr sp ann nm pats -> c sp ann nm (go <$> pats)

patternFoldM
  :: (Monad m)
  => (Span -> ann -> Id -> m b)
  -> (Span -> ann -> m b)
  -> (Span -> ann -> b -> m b)
  -> (Span -> ann -> Int -> m b)
  -> (Span -> ann -> Double -> m b)
  -> (Span -> ann -> Id -> [b] -> m b)
  -> Pattern ann
  -> m b
patternFoldM v w b i f c = go
  where
    go = \case
      PVar sp ann nm -> v sp ann nm
      PWild sp ann -> w sp ann
      PBox sp ann pat ->
        do
            pat' <- go pat
            b sp ann pat'
      PInt sp ann int -> i sp ann int
      PFloat sp ann doub -> f sp ann doub
      PConstr sp ann nm pats ->
        do
            pats' <- mapM go pats
            c sp ann nm pats'

-- | Variables bound by patterns
boundVars :: Pattern a -> [Id]
boundVars (PVar _ _ v)     = [v]
boundVars PWild {}       = []
boundVars (PBox _ _ p)     = boundVars p
boundVars PInt {}        = []
boundVars PFloat {}      = []
boundVars (PConstr _ _ _ ps) = concatMap boundVars ps

boundVarsAndAnnotations :: Pattern a -> [(a, Id)]
boundVarsAndAnnotations =
    patternFold var wild box int flt cstr
    where var  _ ty ident = [(ty, ident)]
          wild _ _        = []
          box _ _ pat     = pat
          int _ _ _       = []
          flt _ _ _       = []
          cstr _ _ _ pats = concat pats

ppair :: Span
      -> a
      -> Pattern a
      -> Pattern a
      -> Pattern a
ppair s annotation left right =
    PConstr s annotation (mkId "(,)") [left, right]

-- >>> runFreshener (PVar ((0,0),(0,0)) (Id "x" "x"))
-- PVar ((0,0),(0,0)) (Id "x" "x_0")

-- | Freshening for patterns
instance Freshenable m (Pattern a) where

  freshen :: Monad m => Pattern a -> Freshener m (Pattern a)
  freshen (PVar s a var) = do
      var' <- freshIdentifierBase ValueL var
      return $ PVar s a var'

  freshen (PBox s a p) = do
      p' <- freshen p
      return $ PBox s a p'

  freshen (PConstr s a name ps) = do
      ps <- mapM freshen ps
      return (PConstr s a name ps)

  freshen p@PWild {} = return p
  freshen p@PInt {} = return p
  freshen p@PFloat {} = return p
