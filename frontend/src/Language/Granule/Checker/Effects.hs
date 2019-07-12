{- Deals with effect algebras -}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Effects where

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Kinds

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span

import Language.Granule.Utils

import Data.List (nub)

effectMult :: (?globals :: Globals) => Span -> Type -> Type -> Checker Type
effectMult sp t1 t2 = do
  k1 <- inferKindOfType sp t1
  k2 <- inferKindOfType sp t2
  if k1 == k2
    then do
      if isPure t1 then return t2
        else if isPure t2 then return t1
        else
         case k1 of
              -- Nat effects
              KPromote (TyCon (internalName -> "Nat")) ->
                return $ TyInfix TyOpPlus t1 t2

              -- IO effects
              KPromote (TyCon (internalName -> "IO")) ->
                case (t1, t2) of
                  -- Actual sets, take the union
                  (TySet ts1, TySet ts2) ->
                    return $ TySet $ nub (ts1 <> ts2)
                  _ -> throw $
                    TypeError { errLoc = sp, tyExpected = TySet [TyVar $ mkId "?"], tyActual = t1 }
              _ -> throw $ UnknownResourceAlgebra { errLoc = sp, errK = k1 }
  else throw $ KindMismatch { errLoc = sp, kExpected = k1, kActual = k2 }
