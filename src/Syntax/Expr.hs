{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Syntax.Expr (Id, Value(..), Expr(..), Type(..), TyCon(..), Def(..), Op(..),
                   CKind(..), Coeffect(..), Effect,
                   uniqueNames, arity, fvs, subst,
                   kindOf, kindJoin, tyCoeffectKind) where

import Data.List
import Control.Monad.Writer
import Control.Monad.Trans.State

type Id = String
data Op = Add | Sub | Mul deriving (Eq, Show)

-- Values in Gram
data Value = Abs Id Expr
           | Num Int
           | Promote Expr
           | Pure Expr
           | Var Id
          deriving (Eq, Show)

-- Expressions (computations) in Gram
data Expr = App Expr Expr
          | Binop Op Expr Expr
          | LetBox Id Type Expr Expr
          | LetDiamond Id Type Expr Expr
          | Val Value
          deriving (Eq, Show)

type Freshener t = StateT Int (Writer [(Id, Id)]) t

class Term t where
  -- Compute the free variables in a term
  fvs :: t -> [Id]
  -- Syntactic substitution of an expression into a term
  -- (assuming variables are all unique to avoid capture)
  subst :: Expr -> Id -> t -> Expr
  -- Freshen
  freshen :: t -> Freshener t

freshVar :: Id -> Freshener Id
freshVar var = do
   v <- get
   let var' = var ++ show v
   put (v+1)
   tell [(var, var')]
   return var'

instance Term Value where
    fvs (Abs x e)   = (fvs e) \\ [x]
    fvs (Var x)     = [x]
    fvs (Pure e)    = fvs e
    fvs (Promote e) = fvs e
    fvs _           = []

    subst es v (Abs w e)        = Val $ Abs w (subst es v e)
    subst es v (Pure e)         = Val $ Pure (subst es v e)
    subst es v (Promote e)      = Val $ Promote (subst es v e)
    subst es v (Var w) | v == w = es
    subst _ _ val               = Val val

    freshen (Abs var e) = do
      var' <- freshVar var
      e'   <- freshen (subst (Val (Var var')) var e)
      return $ Abs var' e'

    freshen (Pure e) = do
      e' <- freshen e
      return $ Pure e'

    freshen (Promote e) = do
      e' <- freshen e
      return $ Promote e'

    freshen v = return v


instance Term Expr where
   fvs (App e1 e2)            = fvs e1 ++ fvs e2
   fvs (Binop _ e1 e2)        = fvs e1 ++ fvs e2
   fvs (LetBox x _ e1 e2)     = fvs e1 ++ ((fvs e2) \\ [x])
   fvs (LetDiamond x _ e1 e2) = fvs e1 ++ ((fvs e2) \\ [x])
   fvs (Val e)                = fvs e

   subst es v (App e1 e2)        = App (subst es v e1) (subst es v e2)
   subst es v (Binop op e1 e2)   = Binop op (subst es v e1) (subst es v e2)
   subst es v (LetBox w t e1 e2) = LetBox w t (subst es v e1) (subst es v e2)
   subst es v (LetDiamond w t e1 e2) = LetDiamond w t (subst es v e1) (subst es v e2)
   subst es v (Val val)          = subst es v val

   freshen (LetBox var t e1 e2) = do
      var' <- freshVar var
      e1'  <- freshen e1
      e2'  <- freshen (subst (Val (Var var')) var e2)
      return $ LetBox var' t e1' e2'

   freshen (App e1 e2) = do
      e1' <- freshen e1
      e2' <- freshen e2
      return $ App e1' e2'

   freshen (LetDiamond var t e1 e2) = do
      var' <- freshVar var
      e1'  <- freshen e1
      e2'  <- freshen (subst (Val (Var var')) var e2)
      return $ LetDiamond var' t e1' e2'

   freshen (Binop op e1 e2) = do
      e1' <- freshen e1
      e2' <- freshen e2
      return $ Binop op e1' e2'

   freshen (Val v) = do
     v' <- freshen v
     return (Val v')


--------- Definitions

data Def = Def Id Expr [Pattern] Type
          deriving (Eq, Show)

type Pattern = Either String String

----------- Types

data TyCon = TyInt
           | TyBool
           | TyVar String -- TyVar not used yet
    deriving (Eq, Show)

data Type = FunTy Type Type
          | ConT TyCon
          | Box Coeffect Type
          | Diamond Effect Type
    deriving (Eq, Show)


arity :: Type -> Int
arity (FunTy _ t) = 1 + arity t
arity _           = 0

type Effect = [String]

-- TODO: split Coeffect type properly into kinds
data Coeffect = Nat Int
              | CVar String
              | CPlus Coeffect Coeffect
              | CTimes Coeffect Coeffect
              | Level Int
    deriving (Eq, Show)

data CKind = CNat | CLevel | CPoly
    deriving (Eq, Show)

-- What is the coeffect kind in this type?
tyCoeffectKind :: Type -> CKind
tyCoeffectKind (FunTy t1 t2) = tyCoeffectKind t1 `kindJoin` tyCoeffectKind t2
tyCoeffectKind (Diamond _ t) = tyCoeffectKind t
tyCoeffectKind (Box c t) = kindOf c `kindJoin` (tyCoeffectKind t)
tyCoeffectKind (ConT _) = CPoly

kindOf :: Coeffect -> CKind
kindOf (Level _)    = CLevel
kindOf (Nat _)      = CNat
kindOf (CPlus n m)  = kindOf n `kindJoin` kindOf m
kindOf (CTimes n m) = kindOf n `kindJoin` kindOf m
kindOf (CVar _)     = CPoly

kindJoin :: CKind -> CKind -> CKind
kindJoin CPoly c       = c
kindJoin c CPoly       = c
kindJoin CLevel CLevel = CLevel
kindJoin CNat CNat     = CNat
kindJoin CLevel _      = CLevel
kindJoin _ CLevel      = CLevel
-- kindJoin c d = error $ "Coeffect kind mismatch " ++ show c ++ " != " ++ show d

-- Alpha-convert all bound variables

uniqueNames :: [Def] -> ([Def], [(Id, Id)])
uniqueNames = runWriter . flip evalStateT (0 :: Int) . mapM uniqueNameDef
  where
    uniqueNameDef (Def var e ps t) = do
      e'  <- freshen e
      ps' <- mapM uniqueNamePat ps
      return $ Def var e' ps' t

    -- TODO: convert renaming map to be build in the WriterT monad
    uniqueNamePat (Left var) = do
      var' <- freshVar var
      return $ Left var'

    uniqueNamePat (Right var) = do
      var' <- freshVar var
      return $ Right var'
