{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Checker.Types where

import Syntax.Expr
import Syntax.Pretty
import Context
import Data.List

type TyOrDisc = Either Type (Coeffect, Type)

-- Given a pattern and its type, construct the binding environment
-- for that pattern
ctxtFromTypedPattern :: Type -> Pattern -> Maybe [(Id, TyOrDisc)]
ctxtFromTypedPattern _             PWild        = Just []
ctxtFromTypedPattern t             (PVar v)     = Just [(v, Left t)]
ctxtFromTypedPattern (ConT "Int")  (PInt _)     = Just []
ctxtFromTypedPattern (ConT "Float") (PFloat _)    = Just []
ctxtFromTypedPattern (Box c t)     (PBoxVar v)  = Just [(v, Right (c, t))]
ctxtFromTypedPattern (ConT "Bool") (PConstr "True")  = Just []
ctxtFromTypedPattern (ConT "Bool") (PConstr "False") = Just []
ctxtFromTypedPattern _             _            = Nothing

instance Pretty (Type, Env TyOrDisc) where
    pretty (t, _) = pretty t

instance Pretty (Id, TyOrDisc) where
    pretty (v, ty) = v ++ " : " ++ pretty ty

instance Pretty TyOrDisc where
    pretty (Left ty) = pretty ty
    pretty (Right (c, ty)) = "|" ++ pretty ty ++ "|." ++ pretty c

instance Pretty (Env TypeScheme) where
   pretty xs = "{" ++ intercalate "," (map pp xs) ++ "}"
     where pp (var, t) = var ++ " : " ++ pretty t

instance Pretty (Env TyOrDisc) where
   pretty xs = "{" ++ intercalate "," (map pp xs) ++ "}"
     where pp (var, Left t) = var ++ " : " ++ pretty t
           pp (var, Right (c, t)) = var ++ " : .[" ++ pretty t ++ "]. " ++ pretty c
