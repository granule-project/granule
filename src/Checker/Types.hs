{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Checker.Types where

import Syntax.Expr
import Syntax.Pretty
import Data.List
import Data.Maybe
import Data.Either
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Control.Monad
import Data.SBV
import qualified Data.Set as S

-- Symbolic coeffects
data SCoeffect =
     SNat   NatModifier SInteger
   | SReal  SReal
   | SLevel SInteger
   | SSet   (S.Set (Id, Type))
  deriving (Show, Eq)

type TyOrDisc = Either Type (Coeffect, Type)

type Env t = [(Id, t)]

extend :: Env a -> Id -> a -> Env a
extend env x v = (x, v) : env

empty :: Env a
empty = []

-- replace an item in an environment
replace :: Env a -> Id -> a -> Env a
replace [] id v
  = [(id, v)]
replace ((id', _):env) id v | id == id'
  = (id', v) : env
replace (x : env) id v
  = x : replace env id v

instance Pretty (Type, Env TyOrDisc) where
    pretty (t, env) = pretty t

instance Pretty (Id, TyOrDisc) where
    pretty (v, ty) = v ++ " : " ++ pretty ty

instance Pretty TyOrDisc where
    pretty (Left ty) = pretty ty
    pretty (Right (c, ty)) = "|" ++ pretty ty ++ "|." ++ pretty c

keyIntersect :: Env a -> Env a -> Env a
keyIntersect a b = sortBy (\a b -> fst a `compare` fst b) $ filter (appearsIn a) b
  where appearsIn a (id, _) = isJust $ lookup id a

{-
vars :: Coeffect -> [String]
vars (CVar v) = [v]
vars (CPlus n m) = vars n ++ vars m
vars (CTimes n m) = vars n ++ vars m
vars _ = []
-}

deleteVar :: Eq a => a -> [(a, b)] -> [(a, b)]
deleteVar _ [] = []
deleteVar x ((y, b) : m) | x == y = deleteVar x m
                         | otherwise = (y, b) : deleteVar x m

unrename :: [(Id, Id)] -> Id -> Id
unrename nameMap var =
    case lookup var (map swap nameMap) of
      Just var' -> var'
      Nothing  -> var
  where swap (a, b) = (b, a)

instance Pretty (Env TypeScheme) where
   pretty xs = "{" ++ intercalate "," (map pp xs) ++ "}"
     where pp (var, t) = var ++ " : " ++ pretty t

instance Pretty (Env TyOrDisc) where
   pretty xs = "{" ++ intercalate "," (map pp xs) ++ "}"
     where pp (var, Left t) = var ++ " : " ++ pretty t
           pp (var, Right (c, t)) = var ++ " : .[" ++ pretty t ++ "]. " ++ pretty c

ctxtFromTypedPattern :: Type -> Pattern -> Maybe [(Id, TyOrDisc)]
ctxtFromTypedPattern t             PWild        = Just []
ctxtFromTypedPattern t             (PVar v)     = Just [(v, Left t)]
ctxtFromTypedPattern (ConT "Int")  (PInt n)     = Just []
ctxtFromTypedPattern (ConT "Real") (PReal n)    = Just []
ctxtFromTypedPattern (Box c t)     (PBoxVar v)  = Just [(v, Right (c, t))]
ctxtFromTypedPattern (ConT "Bool") (PConstr "True")  = Just []
ctxtFromTypedPattern (ConT "Bool") (PConstr "False") = Just []
ctxtFromTypedPattern _             _            = Nothing