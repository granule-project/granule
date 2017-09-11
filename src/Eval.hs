-- Gram interpreter

module Eval (eval) where

import Syntax.Expr
import Syntax.Pretty
import Checker.Types

evalOp :: Num a => Op -> (a -> a -> a)
evalOp Add = (+)
evalOp Sub = (-)
evalOp Mul = (*)

-- Call by value big step semantics
evalIn :: Env Value -> Expr -> IO Value

evalIn env (App (Val (Var "write")) e) = do
    v <- evalIn env e
    putStrLn $ show v
    return $ Pure (Val v)

evalIn _ (Val (Var "read")) = do
    val <- readLn
    return $ Pure (Val (NumInt val))

evalIn _ (Val (Abs x e)) =
    return $ Abs x e

evalIn env (App e1 e2) = do
    v1 <- evalIn env e1
    case v1 of
      Abs x e3 -> do
        v2 <- evalIn env e2
        evalIn env (subst (Val v2) x e3)
      _ -> error "Cannot apply value"

evalIn env (Binop op e1 e2) = do
     v1 <- evalIn env e1
     v2 <- evalIn env e2
     case (v1, v2) of
       (NumInt n1, NumInt n2)   -> return $ NumInt  (evalOp op n1 n2)
       (NumInt n1, NumReal n2)  -> return $ NumReal (evalOp op (cast n1) n2)
       (NumReal n1, NumInt n2)  -> return $ NumReal (evalOp op n1 (cast n2))
       (NumReal n1, NumReal n2) -> return $ NumReal (evalOp op n1 n2)
       _ -> fail $ "Runtime exception: Not a number: "
                 ++ pretty v1 ++ " or " ++ pretty v2
  where
    cast :: Int -> Double
    cast = fromInteger . toInteger

evalIn env (LetBox var _ _ e1 e2) = do
    v1 <- evalIn env e1
    case v1 of
       Promote e1' ->
           evalIn env (subst e1' var e2)
       other -> fail $ "Runtime exception: Expecting a box value but got: "
             ++ pretty other

evalIn env (LetDiamond var _ e1 e2) = do
     v1 <- evalIn env e1
     case v1 of
        Pure e -> do
          val <- evalIn env e
          evalIn env (subst (Val val) var e2)
        other -> fail $ "Runtime exception: Expecting a diamonad value bug got: "
                      ++ pretty other

evalIn env (Val (Var x)) =
    case (lookup x env) of
      Just val -> return val
      Nothing  -> fail $ "Variable '" ++ x ++ "' is undefined in context: "
               ++ show env

evalIn _ (Val v) = return v

evalIn env (Case gExpr cases) = do
    val <- evalIn env gExpr
    pmatch cases val
  where
    pmatch []                _                = error "Incomplete pattern match"
    pmatch ((PWild, e):_)    _                = evalIn env e
    pmatch ((PConstr s, e):_) (Constr s') | s == s' = evalIn env e
    pmatch ((PVar var, e):_) val              = evalIn env (subst (Val val) var e)
    pmatch ((PBoxVar var, e):_) (Promote e')  = evalIn env (subst e' var e)
    pmatch ((PInt n, e):_)  (NumInt m)  | n == m = evalIn env e
    pmatch ((PReal n, e):_) (NumReal m) | n == m = evalIn env e
    pmatch (_:ps)            val              = pmatch ps val

evalDefs :: Env Value -> [Def] -> IO (Env Value)
evalDefs env [] = return env
evalDefs env ((Def var e [] _):defs) = do
    val <- evalIn env e
    evalDefs (extend env var val) defs
evalDefs _ (d : _) =
    error $ "Desugaring must be broken for " ++ show d

eval :: [Def] -> IO Value
eval defs = do
    bindings <- evalDefs empty defs
    case lookup "main" bindings of
      Nothing -> fail "Missing a definition called 'main'"
      Just (Pure e)    -> evalIn bindings e
      Just (Promote e) -> evalIn bindings e
      Just val -> return val
