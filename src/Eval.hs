-- Granule interpreter

module Eval (eval) where

import Syntax.Expr
import Syntax.Pretty
import Syntax.Desugar
import Context

-- Evaluate operators
evalOp :: Num a => Op -> (a -> a -> a)
evalOp Add = (+)
evalOp Sub = (-)
evalOp Mul = (*)

-- Call-by-value big step semantics
evalIn :: Env Value -> Expr -> IO Value

evalIn env (App _ (Val _ (Var "write")) e) = do
    v <- evalIn env e
    print v
    return $ Pure (Val nullSpan v)

evalIn _ (Val s (Var "read")) = do
    val <- readLn
    return $ Pure (Val s (NumInt val))

evalIn _ (Val _ (Abs x t e)) =
    return $ Abs x t e

evalIn env (App _ e1 e2) = do
    v1 <- evalIn env e1
    case v1 of
      Abs x _ e3 -> do
        v2 <- evalIn env e2
        evalIn env (subst (Val nullSpan v2) x e3)

      Constr c vs -> do
        v2 <- evalIn env e2
        return $ Constr c (vs ++ [v2])

      -- _ -> error "Cannot apply value"

evalIn env (Binop _ op e1 e2) = do
     v1 <- evalIn env e1
     v2 <- evalIn env e2
     case (v1, v2) of
       (NumInt n1, NumInt n2)     -> return $ NumInt (evalOp op n1 n2)
       (NumInt n1, NumFloat n2)   -> return $ NumFloat (evalOp op (cast n1) n2)
       (NumFloat n1, NumInt n2)   -> return $ NumFloat (evalOp op n1 (cast n2))
       (NumFloat n1, NumFloat n2) -> return $ NumFloat (evalOp op n1 n2)
       _ -> fail $ "Runtime exception: Not a number: "
                 ++ pretty v1 ++ " or " ++ pretty v2
  where
    cast :: Int -> Double
    cast = fromInteger . toInteger

evalIn env (LetBox _ var _ e1 e2) = do
    v1 <- evalIn env e1
    case v1 of
       Promote e1' ->
           evalIn env (subst e1' var e2)
       other -> fail $ "Runtime exception: Expecting a box value but got: "
             ++ pretty other

evalIn env (LetDiamond _ var _ e1 e2) = do
     v1 <- evalIn env e1
     case v1 of
        Pure e -> do
          val <- evalIn env e
          evalIn env (subst (Val nullSpan val) var e2)
        other -> fail $ "Runtime exception: Expecting a diamonad value bug got: "
                      ++ pretty other

evalIn env (Val _ (Var x)) =
    case lookup x env of
      Just val -> return val
      Nothing  -> fail $ "Variable '" ++ x ++ "' is undefined in context: "
               ++ show env

evalIn _ (Val _ v) = return v

evalIn env (Case _ gExpr cases) = do
    val <- evalIn env gExpr
    p <- pmatch cases val
    case p of
      Just (ei, bindings) -> evalIn env (applyBindings bindings ei)
      Nothing             -> error "Incomplete pattern match"
  where
    applyBindings [] e = e
    applyBindings ((e', var):bs) e = applyBindings bs (subst e' var e)

    pmatch []                _                           = return Nothing
    pmatch ((PWild _, e):_)  _                           = return $ Just (e, [])
    pmatch ((PConstr _ s, e):_) (Constr s' []) | s == s' = return $ Just (e, [])
    pmatch ((PVar _ var, e):_) val                       = return $ Just (e, [(Val nullSpan val, var)])
    pmatch ((PBox _ p, e):ps) (Promote e')      = do
      v <- evalIn env e'
      p <- pmatch [(p, e)] v
      case p of
        Just (_, env) -> do
          return $ Just (e, env)
        Nothing -> pmatch ps (Promote e')

    pmatch ((PInt _ n, e):_)      (NumInt m)   | n == m   = return $ Just (e, [])
    pmatch ((PFloat _ n, e):_)    (NumFloat m) | n == m   = return $ Just (e, [])
    pmatch ((PApp _ p1 p2, e):ps) val@(Constr s vs) = do
      p <- pmatch [(p2, e)] (last vs)
      case p of
        Just (_, bindings) -> do
          p' <- pmatch [(p1, e)] (Constr s (reverse . tail . reverse $ vs))
          case p' of
            Just (_, bindings') -> return $ Just (e, bindings ++ bindings')
            _                   -> pmatch ps val
        _                  -> pmatch ps val
    pmatch (_:ps) val = pmatch ps val

evalDefs :: Env Value -> [Def] -> IO (Env Value)
evalDefs env [] = return env
evalDefs env (Def _ var e [] _ : defs) = do
    val <- evalIn env e
    evalDefs (extend env var val) defs
evalDefs env (d : defs) = do
    evalDefs env (desugar d : defs)

eval :: [Def] -> IO (Maybe Value)
eval defs = do
    bindings <- evalDefs empty defs
    case lookup "main" bindings of
      Nothing -> return Nothing
      Just (Pure e)    -> fmap Just (evalIn bindings e)
      Just (Promote e) -> fmap Just (evalIn bindings e)
      Just val -> return $ Just val
