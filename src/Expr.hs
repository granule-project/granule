{-# LANGUAGE FlexibleInstances #-}

module Expr where

import Data.List

type Id = String
data Op = Add | Sub | Mul deriving (Eq, Show)

data Expr = Abs Id Expr
          | App Expr Expr
          | Var Id
          | Num Int
          | Binop Op Expr Expr
          | Promote Expr
          | LetBox Id Expr Expr
          deriving (Eq, Show)

data Def = Def Id Expr Type
          deriving (Eq, Show)

-- Types

data TyCon = TyInt | TyBool | TyVarInternal String
    deriving (Eq, Show)

data Type = FunTy Type Type | ConT TyCon
    deriving (Eq, Show)

{- Pretty printers -}

class Pretty t where
    pretty :: t -> String

instance Pretty Type where
    pretty (ConT TyInt)  = "Int"
    pretty (ConT TyBool) = "Bool"
    pretty (FunTy t1 t2) = pretty t1 ++ " -> " ++ pretty t2

instance Pretty [Def] where
    pretty = intercalate "\n"
     . map (\(Def v e t) -> v ++ " : " ++ show t ++ "\n" ++ v ++ " = " ++ pretty e)

instance Pretty t => Pretty (Maybe t) where
    pretty Nothing = "unknown"
    pretty (Just x) = pretty x

instance Pretty Expr where
    pretty expr =
      case expr of
        (Abs x e) -> parens $ "\\" ++ x ++ " -> " ++ pretty e
        (App e1 e2) -> parens $ pretty e1 ++ " " ++ pretty e2
        (Binop op e1 e2) -> parens $ pretty e1 ++ prettyOp op ++ pretty e2
        (LetBox v e1 e2) -> parens $ "let [" ++ v ++ "] = " ++ pretty e1 ++ " in " ++ pretty e2
        (Promote e)      -> "[ " ++ pretty e ++ " ]"
        (Var x) -> x
        (Num n) -> show n
     where prettyOp Add = " + "
           prettyOp Sub = " - "
           prettyOp Mul = " * "
           parens s = "(" ++ s ++ ")"

{- Smart constructors -}

addExpr :: Expr -> Expr -> Expr
addExpr = Binop Add

subExpr :: Expr -> Expr -> Expr
subExpr = Binop Sub

mulExpr :: Expr -> Expr -> Expr
mulExpr = Binop Mul
