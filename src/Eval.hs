module Eval (Val(..), eval, Env, extend, empty) where

import Expr

data Val c = FunVal (Env (Val c)) Id (Expr c)
           | NumVal Int
           | BoxVal (Expr c)

instance Pretty Int where
  pretty = show

instance (Show c, Pretty c) => Show (Val c) where
  show (FunVal _ _ _) = "<fun>"
  show (BoxVal e) = pretty e
  show (NumVal n) = show n

type Env a = Id -> a

extend :: Env a -> Id -> a -> Env a
extend e x v = \y -> if x == y then v else e y

empty :: Env a
empty = \v -> error $ "No variable named " ++ v

evalOp :: Op -> (Int -> Int -> Int)
evalOp Add = (+)
evalOp Sub = (-)
evalOp Mul = (*)

-- Call by value big step semantics
evalIn :: Env (Val c) -> Expr c -> Val c
evalIn env (Abs x e) = FunVal env x e
evalIn env (App e1 e2) =
  case evalIn env e1 of
    FunVal env' x e3 ->
      let v2 = evalIn env e2 in
      evalIn (extend env' x v2) e3
    _ -> error "Cannot apply value"
evalIn env (Var x) = env x
evalIn _ (Num n) = NumVal n
evalIn env (Binop op e1 e2) =
  let v1 = evalIn env e1
      v2 = evalIn env e2
      x = evalOp op in
  case (v1,v2) of
    (NumVal n1,NumVal n2) -> NumVal (n1 `x` n2)
    _ -> error "Not a number"

-- GMTT big step semantics (CBN)

evalIn env (LetBox var _ e1 e2) =
   case evalIn env e1 of
      BoxVal e1' ->
        evalIn env (subst e1' var e2)

evalIn env (Promote e) = BoxVal e


evalDefs :: Env (Val c) -> [Def c] -> Env (Val c)
evalDefs env [] = env
evalDefs env ((Def var e _):defs) =
  evalDefs (extend env var (evalIn env e)) defs

eval :: [Def c] -> Val c
eval defs = bindings "main"
  where
    bindings = evalDefs empty defs