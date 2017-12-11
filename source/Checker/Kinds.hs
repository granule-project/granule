-- Mainly provides a kind checker on types
module Checker.Kinds (kindCheck
                    , inferKindOfType
                    , joinCoeffectConstr
                    , hasLub) where

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

import Checker.Monad
import Checker.Predicates
import Checker.Primitives
import Syntax.Expr
import Context

import Data.List (isPrefixOf)

-- Currently we expect that a type scheme has kind KType
kindCheck :: Span -> TypeScheme -> MaybeT Checker ()
kindCheck s (Forall _ quantifiedVariables ty) = do
  kind <- inferKindOfType' s quantifiedVariables ty
  case kind of
    KType -> return ()
    _     -> illKindedNEq s KType kind

inferKindOfType :: Span -> Type -> MaybeT Checker Kind
inferKindOfType s t = do
    checkerState <- get
    inferKindOfType' s (stripQuantifiers $ ckctxt checkerState) t

inferKindOfType' :: Span -> Ctxt Kind -> Type -> MaybeT Checker Kind
inferKindOfType' s quantifiedVariables =
    typeFoldM kFunOrPair kCon kBox kDiamond kVar kApp kInt kFunOrPair kInfix
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

     kApp (KFun k1 k2) kArg | k1 `hasLub` kArg = return k2
     kApp k kArg = illKindedNEq s (KFun kArg (KPoly "a")) k

     kInt _ = return $ KConstr "Nat"

     kInfix op k1 k2 =
       case lookup op typeLevelConstructors of
         Just (KFun k1' (KFun k2' kr)) ->
           if k1 `hasLub` k1'
            then if k2 `hasLub` k2'
                 then return kr
                 else illKindedNEq s k2 k2'
            else illKindedNEq s k1 k1'
         Nothing   -> unknownName s (op ++ " operator.")

hasLub :: Kind -> Kind -> Bool
hasLub k1 k2 | k1 == k2 = True
hasLub (KConstr kc1) (KConstr kc2) =
  case joinCoeffectConstr kc1 kc2 of
    Nothing -> False
    Just _  -> True

joinCoeffectConstr :: String -> String -> Maybe String
joinCoeffectConstr "Nat" n | "Nat" `isPrefixOf` n = Just n
joinCoeffectConstr n "Nat" | "Nat" `isPrefixOf` n = Just n
joinCoeffectConstr "Float" "Nat" = Just "Float"
joinCoeffectConstr "Nat" "Float" = Just "Float"
joinCoeffectConstr _ _ = Nothing
