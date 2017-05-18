module Expr where

import Data.List

type Id = String
data Op = Add | Sub | Mul deriving (Eq, Show)

data Expr = Abs Id Expr
          | App Expr Expr
          | Var Id
          | Num Int
          | Binop Op Expr Expr
          deriving (Eq, Show)

data Def = Def Id Expr Type
          deriving (Eq, Show)

-- Types

data TyCon = TyInt | TyBool
    deriving (Eq, Show)

data Type = FunTy Type Type | ConT TyCon
    deriving (Eq, Show)

{- Pretty printers -}

pretty :: [Def] -> String
pretty = intercalate "\n"
       . map (\(Def v e t) -> v ++ " : " ++ show t ++ "\n" ++ v ++ " = " ++ source e)

source :: Expr -> String
source expr = case expr of
  (Abs x e) -> parens $ "\\" ++ x ++ " -> " ++ source e
  (App e1 e2) -> parens $ source e1 ++ " " ++ source e2
  (Binop op e1 e2) -> parens $ source e1 ++ sourceOp op ++ source e2
  (Var x) -> x
  (Num n) -> show n
  where sourceOp Add = " + "
        sourceOp Sub = " - "
        sourceOp Mul = " * "
        parens s = "(" ++ s ++ ")"

{- Smart constructors -}

addExpr :: Expr -> Expr -> Expr
addExpr = Binop Add

subExpr :: Expr -> Expr -> Expr
subExpr = Binop Sub

mulExpr :: Expr -> Expr -> Expr
mulExpr = Binop Mul
