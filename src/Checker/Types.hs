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


type TyOrDisc = Either Type (Coeffect, Type)

-- The resource semiring class
class Semiring c where
  plus  :: c -> c -> c
  mult  :: c -> c -> c
  one   :: c
  zero  :: c

-- Coeffects are a semiring
-- TODO: Coeffect will get statified later
instance Semiring Coeffect where
  plus (Nat n) (Nat m) = Nat (n + m)
  plus c d = CPlus c d
  mult (Nat n) (Nat m) = Nat (n * m)
  mult c d = CTimes c d
  one = Nat 1
  zero = Nat 0

oneKind :: CKind -> Coeffect
oneKind CPoly = Nat 1
oneKind CNat = Nat 1
oneKind CLevel = Level 1

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


-- Given an environment, derelict and discharge all variables which are not discharged
multAll :: [Id] -> Coeffect -> Env TyOrDisc -> Env TyOrDisc

multAll _ _ []
    = []

multAll vars c ((id, Left t) : env) | id `elem` vars
    = (id, Right (c, t)) : multAll vars c env

multAll vars c ((id, Right (c', t)) : env) | id `elem` vars
    = (id, Right (c `mult` c', t)) : multAll vars c env

multAll vars c ((id, Left t) : env) = multAll vars c env
multAll vars c ((id, Right (_, t)) : env) = multAll vars c env

instance Pretty (Type, Env TyOrDisc) where
    pretty (t, env) = pretty t


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
  case lookup var nameMap of
    Just var' -> var'
    Nothing  -> var

instance Pretty (Env Type) where
   pretty xs = "{" ++ intercalate "," (map pp xs) ++ "}"
     where pp (var, t) = var ++ " : " ++ pretty t

instance Pretty (Env TyOrDisc) where
   pretty xs = "{" ++ intercalate "," (map pp xs) ++ "}"
     where pp (var, Left t) = var ++ " : " ++ pretty t
           pp (var, Right (c, t)) = var ++ " : .[" ++ pretty t ++ "]. " ++ pretty c

ctxtFromTypedPattern :: Type -> Pattern -> Maybe [(Id, TyOrDisc)]
ctxtFromTypedPattern t             PWild        = Just []
ctxtFromTypedPattern t             (PVar v)     = Just [(v, Left t)]
ctxtFromTypedPattern (ConT TyInt)  (PInt n)     = Just []
ctxtFromTypedPattern (Box c t)     (PBoxVar v)  = Just [(v, Right (c, t))]
ctxtFromTypedPattern _             _            = Nothing