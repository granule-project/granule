{-# LANGUAGE ImplicitParams #-}

module Checker.Exhaustivity (isIrrefutable) where

import Control.Monad.Trans.Maybe
import Control.Monad.State.Strict

import Checker.Monad
import Syntax.Expr
import Utils

-- | Check whether a given pattern match will always succeed
-- NB: This is work in progress.
isIrrefutable :: (?globals :: Globals ) => Span -> Type -> Pattern -> MaybeT Checker Bool
isIrrefutable s t (PVar _ _) = return True
isIrrefutable s t (PWild _)  = return True
isIrrefutable s (PairTy t1 t2) (PPair _ p1 p2) = do
    g1 <- isIrrefutable s t1 p1
    g2 <- isIrrefutable s t2 p2
    return (g1 && g2)
isIrrefutable s (Box _ t) (PBox _ p) = isIrrefutable s t p
isIrrefutable s t@(TyVar _) (PBox _ p) = isIrrefutable s t p
isIrrefutable s (TyCon c) _ = checkCardinality c
isIrrefutable s t@(TyApp t1 t2) (PConstr _ name ps) = unpeel s t (reverse ps)
isIrrefutable s _ _ = return False

-- | Check if every sub-pattern of a type application is also irrefutable
-- (reverse the patterns coming out of a PConstr before calling this)
unpeel :: (?globals :: Globals ) => Span -> Type -> [Pattern] -> MaybeT Checker Bool
unpeel s (TyApp t1 t2) (p:ps) = do
    irrefutable <- isIrrefutable s t2 p
    if irrefutable then unpeel s t1 ps else return False
unpeel _ (TyCon c) _ = checkCardinality c

-- | Get the number of data constructors, only irrefutable if = `Just 1`
checkCardinality :: (?globals :: Globals ) => Id -> MaybeT Checker Bool
checkCardinality tyCon = do
    st <- get
    case lookup tyCon (typeConstructors st) of
      Just (_,Just 1) -> return True
      _               -> return False
