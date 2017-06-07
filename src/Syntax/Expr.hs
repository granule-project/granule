{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Syntax.Expr where

import Data.List
import Control.Monad.State.Strict

type Id = String
data Op = Add | Sub | Mul deriving (Eq, Show)

data Expr = Abs Id Expr
          | App Expr Expr
          | Var Id
          | Num Int
          | Binop Op Expr Expr
          | Promote Expr
          | LetBox Id Type Expr Expr
          | Pure Expr
          | LetDiamond Id Type Expr Expr
          deriving (Eq, Show)

-- Compute the free variables in an expression
fvs :: Expr -> [Id]
fvs (Abs x e) = (fvs e) \\ [x]
fvs (App e1 e2) = fvs e1 ++ fvs e2
fvs (Var x)   = [x]
fvs (Binop _ e1 e2) = fvs e1 ++ fvs e2
fvs (Promote e) = fvs e
fvs (LetBox x _ e1 e2) = fvs e1 ++ ((fvs e2) \\ [x])
fvs (Pure e) = fvs e
fvs (LetDiamond x _ e1 e2) = fvs e1 ++ ((fvs e2) \\ [x])
fvs _ = []

-- Syntactic substitution (assuming variables are all unique)
subst :: Expr -> Id -> Expr -> Expr
subst es v (Abs w e)          = Abs w (subst es v e)
subst es v (App e1 e2)        = App (subst es v e1) (subst es v e2)
subst es v (Binop op e1 e2)   = Binop op (subst es v e1) (subst es v e2)
subst es v (Promote e)        = Promote (subst es v e)
subst es v (LetBox w t e1 e2) = LetBox w t (subst es v e1) (subst es v e2)
subst es v (Pure e)           = Pure (subst es v e)
subst es v (LetDiamond w t e1 e2) = LetDiamond w t (subst es v e1) (subst es v e2)
subst es v (Var w) | v == w = es
subst es v e = e

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
tyCoeffectKind (Box c t) = kind c `kindJoin` (tyCoeffectKind t)
tyCoeffectKind (ConT _) = CPoly

kind :: Coeffect -> CKind
kind (Level _)    = CLevel
kind (Nat _)      = CNat
kind (CPlus n m)  = kind n `kindJoin` kind m
kind (CTimes n m) = kind n `kindJoin` kind m
kind (CVar c)  = CPoly

kindJoin CPoly c       = c
kindJoin c CPoly       = c
kindJoin CLevel CLevel = CLevel
kindJoin CNat CNat     = CNat
kindJoin CLevel _      = CLevel
kindJoin _ CLevel      = CLevel
kindJoin c d = error $ "Coeffect kind mismatch " ++ show c ++ " != " ++ show d


{- Smart constructors -}

addExpr :: Expr -> Expr -> Expr
addExpr = Binop Add

subExpr :: Expr -> Expr -> Expr
subExpr = Binop Sub

mulExpr :: Expr -> Expr -> Expr
mulExpr = Binop Mul

uniqueNames :: [Def] -> ([Def], [(Id, Id)])
uniqueNames = flip evalState (0 :: Int) . mapFoldMSnd uniqueNameDef
  where
    mapFoldMSnd :: Monad m => (a -> m (b, [c])) -> [a] -> m ([b], [c])
    mapFoldMSnd f xs = foldM (composer f) ([], []) xs
      where composer f (bs, cs) a = do
              (b, cs') <- f a
              return (bs ++ [b], cs ++ cs')

    uniqueNameDef (Def id e ps t) = do
      (e', rs)   <- uniqueNameExpr e
      (ps', rs') <- mapFoldMSnd uniqueNamePat ps
      return $ (Def id e' ps' t, rs ++ rs')

    freshen id = do
      v <- get
      let id' = id ++ show v
      put (v+1)
      return id'

    -- TODO: convert renaming map to be build in the WriterT monad
    uniqueNamePat (Left id) = do
      id' <- freshen id
      return $ (Left id', [(id', id)])

    uniqueNamePat (Right id) = do
      id' <- freshen id
      return $ (Right id', [(id',  id)])

    uniqueNameExpr (Abs id e) = do
      id' <- freshen id
      (e', rs) <- uniqueNameExpr (subst (Var id') id e)
      return $ (Abs id' e', (id', id) : rs)

    uniqueNameExpr (LetBox id t e1 e2) = do
      id' <- freshen id
      (e1', rs1) <- uniqueNameExpr e1
      (e2', rs2) <- uniqueNameExpr (subst (Var id') id e2)
      return $ (LetBox id' t e1' e2', (id', id) : (rs1 ++ rs2))

    uniqueNameExpr (App e1 e2) = do
      (e1', rs1) <- uniqueNameExpr e1
      (e2', rs2) <- uniqueNameExpr e2
      return $ (App e1' e2', rs1 ++ rs2)

    uniqueNameExpr (LetDiamond id t e1 e2) = do
      id' <- freshen id
      (e1', rs1) <- uniqueNameExpr e1
      (e2', rs2) <- uniqueNameExpr (subst (Var id') id e2)
      return $ (LetDiamond id' t e1' e2', (id', id) : rs1 ++ rs2)

    uniqueNameExpr (Pure e) = do
      (e', rs) <- uniqueNameExpr e
      return $ (Pure e', rs)

    uniqueNameExpr (Binop op e1 e2) = do
      (e1', rs1) <- uniqueNameExpr e1
      (e2', rs2) <- uniqueNameExpr e2
      return $ (Binop op e1' e2', rs1 ++ rs2)

    uniqueNameExpr (Promote e) = do
      (e', rs) <- uniqueNameExpr e
      return $ (Promote e', rs)

    uniqueNameExpr c = return (c, [])

fst3 (a, b, c) = a
snd3 (a, b, c) = b
thd3 (a, b, c) = c
