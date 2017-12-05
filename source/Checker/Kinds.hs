-- Mainly provides a kind checker on types
module Checker.Kinds (kindCheck, inferKindOfType) where

import Control.Monad.Trans.Maybe

import Checker.Monad
import Checker.Primitives
import Syntax.Expr
import Context

-- Currently we expect that a type scheme has kind KType
kindCheck :: Span -> TypeScheme -> MaybeT Checker ()
kindCheck s (Forall _ quantifiedVariables ty) = do
  kind <- inferKindOfType s quantifiedVariables ty
  case kind of
    KType -> return ()
    _     -> illKindedNEq s KType kind

inferKindOfType :: Span -> Ctxt Kind -> Type -> MaybeT Checker Kind
inferKindOfType s quantifiedVariables =
    typeFoldM kFunOrPair kCon kBox kDiamond kVar kApp kInt kFunOrPair
  where
     kFunOrPair KType KType = return KType
     kFunOrPair KType y = illKindedNEq s KType y
     kFunOrPair x _     = illKindedNEq s KType x

     kCon conId =
      case lookup conId typeLevelConstructors of
        Just kind -> return kind
        Nothing   -> unknownName s (conId ++ " constructor.")

     kBox _ KType = return KType
     kBox _ x = illKindedNEq s KType x

     kDiamond _ KType = return KType
     kDiamond _ x     = illKindedNEq s KType x

     kVar tyVar =
      case lookup tyVar quantifiedVariables of
        Just kind -> return kind
        Nothing   -> unknownName s $ tyVar ++ " is unbound (not quantified)."

     kApp (KFun k1 k2) kArg | k1 == kArg = return k2
     kApp k kArg = illKindedNEq s (KFun kArg (KPoly "a")) k

     kInt _ = return $ KConstr "Nat"
