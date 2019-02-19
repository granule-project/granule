{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Exhaustivity (isIrrefutable) where

import Control.Monad.Trans.Maybe
import Control.Monad.State.Strict

import Language.Granule.Checker.Monad
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Utils
--import Language.Granule.Syntax.Pretty

-- | Check whether a given pattern match will always succeed
-- NB: This is work in progress.
isIrrefutable :: (?globals :: Globals, Show t) => Span -> Type -> Pattern t -> MaybeT Checker Bool
isIrrefutable s t (PVar _ _ _) = return True
isIrrefutable s t (PWild _ _)  = return True
isIrrefutable s t (PBox _ _ p) = isIrrefutable s t p

-- TODO: Get rid of types and lookup cardinality through the
-- environment based on the constructor name
isIrrefutable s (TyCon c) (PConstr _ _ _ ps) = do
  irrefutables <- mapM (isIrrefutable s (TyCon c)) ps
  singleton <- checkCardinality c
  return $ singleton && and irrefutables

isIrrefutable s t (PConstr _ _ (internalName -> ",") [p1, p2]) = do
  i1 <- isIrrefutable s t p1
  i2 <- isIrrefutable s t p2
  return (i1 && i2)

isIrrefutable s _ _ = return False

{-
-- | Check if every sub-pattern of a type application is also irrefutable
-- (reverse the patterns coming out of a PConstr before calling this)
unpeel :: (?globals :: Globals) => Span -> Type -> [Pattern t] -> MaybeT Checker Bool
unpeel s (TyApp t1 t2) (p:ps) = do
    irrefutable <- isIrrefutable s t2 p
    if irrefutable then unpeel s t1 ps else return False
unpeel _ (TyCon c) _ = checkCardinality c
unpeel _ _ _ = return False
-}

-- | Get the number of data constructors, only irrefutable if = `Just 1`
checkCardinality :: (?globals :: Globals) => Id -> MaybeT Checker Bool
checkCardinality tyCon = do
    st <- get
    case lookup tyCon (typeConstructors st) of
      Just (_,Just 1) -> return True
      _               -> return False
