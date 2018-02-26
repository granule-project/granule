-- Granule interpreter
{-# LANGUAGE ImplicitParams #-}
module Eval (eval) where

import Syntax.Expr
import Syntax.Pretty
import Syntax.Desugar
import Context
import Utils
import Data.Text (pack)
import qualified Data.Text.IO as Text

import System.IO (hFlush, stdout)

evalBinOp :: String -> Value -> Value -> Value
evalBinOp "+" (NumInt n1) (NumInt n2) = NumInt (n1 + n2)
evalBinOp "*" (NumInt n1) (NumInt n2) = NumInt (n1 * n2)
evalBinOp "-" (NumInt n1) (NumInt n2) = NumInt (n1 - n2)
evalBinOp "+" (NumFloat n1) (NumFloat n2) = NumFloat (n1 + n2)
evalBinOp "*" (NumFloat n1) (NumFloat n2) = NumFloat (n1 * n2)
evalBinOp "-" (NumFloat n1) (NumFloat n2) = NumFloat (n1 - n2)
evalBinOp "==" (NumInt n) (NumInt m) = Constr (mkId . show $ (n == m)) []
evalBinOp "<=" (NumInt n) (NumInt m) = Constr (mkId . show $ (n <= m)) []
evalBinOp "<" (NumInt n) (NumInt m) = Constr (mkId . show $ (n < m)) []
evalBinOp ">=" (NumInt n) (NumInt m) = Constr (mkId . show $ (n >= m)) []
evalBinOp ">" (NumInt n) (NumInt m) = Constr (mkId . show $ (n > m)) []
evalBinOp "==" (NumFloat n) (NumFloat m) = Constr (mkId . show $ (n == m)) []
evalBinOp "<=" (NumFloat n) (NumFloat m) = Constr (mkId . show $ (n <= m)) []
evalBinOp "<" (NumFloat n) (NumFloat m) = Constr (mkId . show $ (n < m)) []
evalBinOp ">=" (NumFloat n) (NumFloat m) = Constr (mkId . show $ (n >= m)) []
evalBinOp ">" (NumFloat n) (NumFloat m) = Constr (mkId . show $ (n > m)) []
evalBinOp op v1 v2 = error $ "Unknown operator " ++ op
                             ++ " on " ++ show v1 ++ " and " ++ show v2

-- Call-by-value big step semantics
evalIn :: Ctxt Value -> Expr -> IO Value

evalIn ctxt (App _ (Val _ (Var v)) e) | internalName v == "write" = do
    StringLiteral s <- evalIn ctxt e
    Text.putStrLn s
    return $ Pure (Val nullSpan (Constr (mkId "()") []))

evalIn _ (Val s (Var v)) | internalName v == "read" = do
    putStr "> "
    hFlush stdout
    val <- Text.getLine
    return $ Pure (Val s (StringLiteral val))

evalIn _ (Val s (Var v)) | internalName v == "readInt" = do
    putStr "> "
    hFlush stdout
    val <- readLn
    return $ Pure (Val s (NumInt val))

evalIn ctxt (App _ (Val _ (Var v)) e) | internalName v == "pure" = do
  v <- evalIn ctxt e
  return $ Pure (Val nullSpan v)

evalIn ctxt (App _ (Val _ (Var v)) e) | internalName v == "intToFloat" = do
  NumInt n <- evalIn ctxt e
  return $ NumFloat (cast n)
  where
    cast :: Int -> Double
    cast = fromInteger . toInteger

evalIn ctxt (App _ (Val _ (Var v)) e) | internalName v == "showInt" = do
  n <- evalIn ctxt e
  case n of
    NumInt n -> return . StringLiteral . pack . show $ n
    n -> error $ show n

evalIn _ (Val _ (Abs p t e)) = return $ Abs p t e

evalIn ctxt (App _ e1 e2) = do
    v1 <- evalIn ctxt e1
    case v1 of
      Abs p _ e3 -> do
        v2 <- evalIn ctxt e2
        p <- pmatch ctxt [(p, e3)] v2
        case p of
          Just (e3, bindings) -> evalIn ctxt (applyBindings bindings e3)

      Constr c vs -> do
        v2 <- evalIn ctxt e2
        return $ Constr c (vs ++ [v2])

      _ -> error $ show v1
      -- _ -> error "Cannot apply value"

evalIn ctxt (Binop _ op e1 e2) = do
     v1 <- evalIn ctxt e1
     v2 <- evalIn ctxt e2
     return $ evalBinOp op v1 v2

evalIn ctxt (LetDiamond _ p _ e1 e2) = do
     v1 <- evalIn ctxt e1
     case v1 of
       Pure e -> do
         v1' <- evalIn ctxt e
         p  <- pmatch ctxt [(p, e2)] v1'
         case p of
           Just (e2, bindings) -> evalIn ctxt (applyBindings bindings e2)
       other -> fail $ "Runtime exception: Expecting a diamonad value bug got: "
                      ++ pretty other

evalIn _ (Val _ (Var v)) | internalName v == "scale" = return
  (Abs (PVar nullSpan $ mkId " x") Nothing (Val nullSpan
    (Abs (PVar nullSpan $ mkId " y") Nothing (
      letBox nullSpan (PVar nullSpan $ mkId " ye")
         (Val nullSpan (Var (mkId " y")))
         (Binop nullSpan
           "*" (Val nullSpan (Var (mkId " x"))) (Val nullSpan (Var (mkId " ye"))))))))

evalIn ctxt (Val _ (Var x)) =
    case lookup x ctxt of
      Just val -> return val
      Nothing  -> fail $ "Variable '" ++ sourceName x ++ "' is undefined in context."

evalIn ctxt (Val s (Pair l r)) = do
  l' <- evalIn ctxt l
  r' <- evalIn ctxt r
  return $ Pair (Val s l') (Val s r')

evalIn _ (Val _ v) = return v

evalIn ctxt (Case _ gExpr cases) = do
    val <- evalIn ctxt gExpr
    p <- pmatch ctxt cases val
    case p of
      Just (ei, bindings) -> evalIn ctxt (applyBindings bindings ei)
      Nothing             ->
        error $ "Incomplete pattern match:\n  cases: " ++ show cases ++ "\n  val: " ++ show val

applyBindings :: Ctxt Expr -> Expr -> Expr
applyBindings [] e = e
applyBindings ((var, e'):bs) e = applyBindings bs (subst e' var e)

pmatch :: Ctxt Value -> [(Pattern, Expr)] -> Value -> IO (Maybe (Expr, Ctxt Expr))
pmatch _ [] _ =
   return Nothing

pmatch _ ((PWild _, e):_)  _ =
   return $ Just (e, [])

pmatch _ ((PConstr _ s ps, e):_) (Constr s' []) | s == s' =
   return $ Just (e, [])

pmatch _ ((PVar _ var, e):_) val =
   return $ Just (e, [(var, Val nullSpan val)])

pmatch ctxt ((PBox _ p, e):ps) (Promote e') = do
  v <- evalIn ctxt e'
  match <- pmatch ctxt [(p, e)] v
  case match of
    Just (_, bindings) -> return $ Just (e, bindings)
    Nothing -> pmatch ctxt ps (Promote e')

pmatch _ ((PInt _ n, e):_)      (NumInt m)   | n == m  =
   return $ Just (e, [])

pmatch _ ((PFloat _ n, e):_)    (NumFloat m) | n == m =
   return $ Just (e, [])

-- pmatch ctxt ((PApp _ p1 p2, e):ps) val@(Constr s vs) = do
--   p <- pmatch ctxt [(p2, e)] (last vs)
--   case p of
--     Just (_, bindings) -> do
--       p' <- pmatch ctxt [(p1, e)] (Constr s (init $ vs))
--       case p' of
--         Just (_, bindings') -> return $ Just (e, bindings ++ bindings')
--         _                   -> pmatch ctxt ps val
--     _                  -> pmatch ctxt ps val

pmatch ctxt ((PPair _ p1 p2, e):ps) vals@(Pair (Val _ v1) (Val _ v2)) = do
  match1 <- pmatch ctxt [(p1, e)] v1
  match2 <- pmatch ctxt [(p2, e)] v2
  case match1 of
    Nothing -> pmatch ctxt ps vals
    Just (_, bindings1) -> case match2 of
      Nothing -> pmatch ctxt ps vals
      Just (_, bindings2) -> return (Just (e, bindings1 ++ bindings2))

pmatch ctxt (_:ps) val = pmatch ctxt ps val

evalDefs :: (?globals :: Globals) => Ctxt Value -> AST -> IO (Ctxt Value)
evalDefs ctxt [] = return ctxt
evalDefs ctxt (Def _ var e [] _ : defs) = do
    val <- evalIn ctxt e
    evalDefs (extend ctxt var val) defs
evalDefs ctxt (ADT {} : defs) = evalDefs ctxt defs
evalDefs ctxt (d : defs) = do
    let d' = desugar d
    debugM "Desugaring" $ pretty d'
    evalDefs ctxt (d' : defs)

eval :: (?globals :: Globals) => AST -> IO (Maybe Value)
eval defs = do
    bindings <- evalDefs empty defs
    case lookup (mkId "main") bindings of
      Nothing -> return Nothing
      Just (Pure e)    -> fmap Just (evalIn bindings e)
      Just (Promote e) -> fmap Just (evalIn bindings e)
      Just val         -> return $ Just val
