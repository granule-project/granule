module Eval (Val(..), eval, Env, extend, empty) where

import Expr
import Debug.Trace

data Val = FunVal (Env Val) Id Expr
         | NumVal Int
         | BoxVal Expr
         | DiamondVal Expr

instance Pretty Int where
  pretty = show

instance Show Val where
  show (FunVal _ _ _) = "<fun>"
  show (BoxVal e) = "[" ++ pretty e ++ "]"
  show (DiamondVal e) = "<" ++ pretty e ++ ">"
  show (NumVal n) = show n

type Env a = [(Id, a)]

extend :: Env a -> Id -> a -> Env a
extend env x v = (x, v) : env

empty :: Env a
empty = []

evalOp :: Op -> (Int -> Int -> Int)
evalOp Add = (+)
evalOp Sub = (-)
evalOp Mul = (*)

-- Call by value big step semantics
evalIn :: Env Val -> Expr -> IO Val

evalIn env (App (Var "write") e) = do
  v <- evalIn env e
  putStrLn $ show v
  return $ v

evalIn env (Var "read") = do
  val <- readLn
  return $ DiamondVal (Num val)

evalIn env (Abs x e) =
  return $ FunVal env x e

evalIn env (App e1 e2) = do
  v1 <- evalIn env e1
  case v1 of
    FunVal env' x e3 -> do
      v2 <- evalIn env e2
      evalIn (extend (env ++ env') x v2) e3
    _ -> error "Cannot apply value"

evalIn env (Var x) =
  case (lookup x env) of
    Just val -> return val
    Nothing  -> fail $ "Variable '" ++ x ++ "' is undefined in context: " ++ show env

evalIn _ (Num n) =
  return $ NumVal n

evalIn env (Binop op e1 e2) = do
   v1 <- evalIn env e1
   v2 <- evalIn env e2
   let x = evalOp op
   case (v1,v2) of
     (NumVal n1, NumVal n2) -> return $ NumVal (n1 `x` n2)
     _ -> error $ "Not a number: " ++ show v1 ++ " or " ++ show v2

-- GMTT big step semantics (CBN)

evalIn env (LetBox var _ e1 e2) = do
   v1 <- evalIn env e1
   case v1 of
      BoxVal e1' ->
        evalIn env (subst e1' var e2)

evalIn env (LetDiamond var _ e1 e2) = do
   v1 <- evalIn env e1
   case v1 of
      DiamondVal e -> do
        val <- evalIn env e
        evalIn env (subst (toExpr val) var e2)


evalIn env (Promote e) = return $ BoxVal e

evalIn env (Pure e) = return $ DiamondVal e



toExpr (FunVal _ i e) = Abs i e
toExpr (NumVal i) = Num i
toExpr (DiamondVal e) = Promote e
toExpr (BoxVal e) = Pure e

evalDefs :: Env Val -> [Def] -> IO (Env Val)
evalDefs env [] = return env
evalDefs env ((Def var e _):defs) = do
  val <- evalIn env e
  evalDefs (extend env var val) defs

eval :: [Def] -> IO Val
eval defs = do
  bindings <- evalDefs empty defs
  case lookup "main" bindings of
    Nothing -> fail "Missing a definition called 'main'"
    Just (DiamondVal e) -> evalIn bindings e
    Just (BoxVal e)     -> evalIn bindings e
    Just val -> return val
