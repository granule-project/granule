module Expr where

type Id = String

data Op = Add | Sub | Mul deriving (Eq,Show)

data Expr = Abs Id Expr
          | App Expr Expr
          | Var Id
          | Num Int
          | Binop Op Expr Expr
          deriving (Eq,Show)

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

addExpr :: Expr -> Expr -> Expr
addExpr = Binop Add

subExpr :: Expr -> Expr -> Expr
subExpr = Binop Sub

mulExpr :: Expr -> Expr -> Expr
mulExpr = Binop Mul
