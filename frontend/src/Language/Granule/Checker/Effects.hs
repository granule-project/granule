{- Deals with effect algebras -}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Effects where

import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Primitives (setLike)

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span

import Language.Granule.Utils

import Data.List (nub)

-- `isEffUnit sp effTy eff` checks whether `eff` of effect type `effTy`
-- is equal to the unit element of the algebra.
isEffUnit :: (?globals :: Globals) => Span -> Type -> Type -> Checker Bool
isEffUnit s effTy eff =
    case effTy of
        -- Nat case
        TyCon (internalName -> "Nat") -> do
            nat <- compileNatKindedTypeToCoeffect s eff
            addConstraint (Eq s (CNat 0) nat (TyCon $ mkId "Nat"))
            return True
        -- Session singleton case
        TyCon (internalName -> "Com") -> do
            return True
        -- IO set case
        -- Any union-set effects, like IO
        TyCon c | setLike c ->
            case eff of
                (TySet []) -> return True
                _          -> return False
        -- Unknown
        _ -> throw $ UnknownResourceAlgebra { errLoc = s, errTy = effTy }

effectMult :: Span -> Type -> Type -> Type -> Checker Type
effectMult sp effTy t1 t2 = do
  if isPure t1 then return t2
  else if isPure t2 then return t1
    else
      case effTy of
        -- Nat effects
        TyCon (internalName -> "Nat") ->
          return $ TyInfix TyOpPlus t1 t2

        -- Com (Session), so far just a singleton
        TyCon (internalName -> "Com") ->
          return $ TyCon $ mkId "Session"

        -- Any union-set effects, like IO
        TyCon c | setLike c ->
          case (t1, t2) of
            -- Actual sets, take the union
            (TySet ts1, TySet ts2) ->
              return $ TySet $ nub (ts1 <> ts2)
            _ -> throw $
                  TypeError { errLoc = sp, tyExpected = TySet [TyVar $ mkId "?"], tyActual = t1 }
        _ -> throw $
               UnknownResourceAlgebra { errLoc = sp, errTy = effTy }