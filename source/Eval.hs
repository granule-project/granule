-- Granule interpreter
{-# LANGUAGE ImplicitParams #-}
module Eval where

import Syntax.Expr
import Syntax.Pretty
import Syntax.Desugar
import Context
import Utils
import Data.Text (pack, unpack, append)
import qualified Data.Text.IO as Text
import Control.Monad (zipWithM)

import qualified Control.Concurrent as C (forkIO)
import qualified Control.Concurrent.Chan as CC (newChan, writeChan, readChan)

import System.IO (hFlush, stdout)
import qualified System.IO as SIO

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
evalBinOp op v1 v2 = error $ "Unknown operator " <> op
                             <> " on " <> show v1 <> " and " <> show v2

-- Call-by-value big step semantics
evalIn :: Ctxt Value -> Expr -> IO Value

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

evalIn _ (Val _ (Abs p t e)) = return $ Abs p t e

evalIn ctxt (App _ e1 e2) = do
    v1 <- evalIn ctxt e1
    case v1 of
      Primitive k -> do
        v2 <- evalIn ctxt e2
        k v2

      Abs p _ e3 -> do
        p <- pmatchTop ctxt [(p, e3)] e2
        case p of
          Just (e3, bindings) -> evalIn ctxt (applyBindings bindings e3)

      Constr c vs -> do
        v2 <- evalIn ctxt e2
        return $ Constr c (vs <> [v2])

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
                      <> prettyDebug other

evalIn _ (Val _ (Var v)) | internalName v == "scale" = return
  (Abs (PVar nullSpan $ mkId " x") Nothing (Val nullSpan
    (Abs (PVar nullSpan $ mkId " y") Nothing (
      letBox nullSpan (PVar nullSpan $ mkId " ye")
         (Val nullSpan (Var (mkId " y")))
         (Binop nullSpan
           "*" (Val nullSpan (Var (mkId " x"))) (Val nullSpan (Var (mkId " ye"))))))))

evalIn ctxt (Val _ (Var x)) =
    case lookup x ctxt of
      Just val@(PrimitiveClosure f) -> return $ Primitive (f ctxt)
      Just val -> return val
      Nothing  -> fail $ "Variable '" <> sourceName x <> "' is undefined in context."

evalIn ctxt (Val s (Pure e)) = do
  v <- evalIn ctxt e
  return $ Pure (Val s v)

evalIn _ (Val _ v) = return v

evalIn ctxt (Case _ guardExpr cases) = do
    p <- pmatchTop ctxt cases guardExpr
    case p of
      Just (ei, bindings) -> evalIn ctxt (applyBindings bindings ei)
      Nothing             ->
        error $ "Incomplete pattern match:\n  cases: "
             <> prettyUser cases <> "\n  expr: " <> prettyUser guardExpr

applyBindings :: Ctxt Expr -> Expr -> Expr
applyBindings [] e = e
applyBindings ((var, e'):bs) e = applyBindings bs (subst e' var e)

{-| Start pattern matching here passing in a context of values
    a list of cases (pattern-expression pairs) and the guard expression.
    If there is a matching pattern p_i then return Just of the branch
    expression e_i and a list of bindings in scope -}
pmatchTop ::
  Ctxt Value -> [(Pattern, Expr)] -> Expr -> IO (Maybe (Expr, Ctxt Expr))
pmatchTop ctxt ((PBox _ (PVar _ var), branchExpr):_) guardExpr = do
  Promote e <- evalIn ctxt guardExpr
  return (Just (subst e var branchExpr, []))

pmatchTop ctxt ((PBox _ (PWild _), branchExpr):_) guardExpr = do
  Promote _ <- evalIn ctxt guardExpr
  return (Just (branchExpr, []))

pmatchTop ctxt ps guardExpr = do
  val <- evalIn ctxt guardExpr
  pmatch ctxt ps val

pmatch ::
  Ctxt Value -> [(Pattern, Expr)] -> Value -> IO (Maybe (Expr, Ctxt Expr))
pmatch _ [] _ =
   return Nothing

pmatch _ ((PWild _, e):_)  _ =
   return $ Just (e, [])

pmatch ctxt ((PConstr _ s innerPs, e):ps) (Constr s' vs) | s == s' = do
   matches <- zipWithM (\p v -> pmatch ctxt [(p, e)] v) innerPs vs
   case sequence matches of
     Just ebindings -> return $ Just (e, concat $ map snd ebindings)
     Nothing        -> pmatch ctxt ps (Constr s' vs)

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

pmatch ctxt (_:ps) val = pmatch ctxt ps val

builtIns :: Ctxt Value
builtIns =
  [
    (mkId "div", Primitive $ \(NumInt n1)
          -> return $ Primitive $ \(NumInt n2) ->
              return $ NumInt (n1 `div` n2))
  , (mkId "pure",       Primitive $ \v -> return $ Pure (Val nullSpan v))
  , (mkId "intToFloat", Primitive $ \(NumInt n) -> return $ NumFloat (cast n))
  , (mkId "showInt",    Primitive $ \n -> case n of
                              NumInt n -> return . StringLiteral . pack . show $ n
                              n        -> error $ show n)
  , (mkId "write", Primitive $ \(StringLiteral s) -> do
                              Text.putStrLn s
                              return $ Pure (Val nullSpan (Constr (mkId "()") [])))
  , (mkId "openFile", Primitive openFile)
  , (mkId "hGetChar", Primitive hGetChar)
  , (mkId "hPutChar", Primitive hPutChar)
  , (mkId "hClose",   Primitive hClose)
  , (mkId "showChar",
        Primitive $ \(CharLiteral c) -> return $ StringLiteral $ pack [c])
  , (mkId "stringAppend",
        Primitive $ \(StringLiteral s) -> return $
          Primitive $ \(StringLiteral t) -> return $ StringLiteral $ s `append` t)
  , (mkId "isEOF", Primitive $ \(Handle h) -> do
        b <- SIO.isEOF
        let boolflag =
             case b of
               True -> Constr (mkId "True") []
               False -> Constr (mkId "False") []
        return . Pure . Val nullSpan $ Constr (mkId ",") [Handle h, boolflag])
  , (mkId "fork", PrimitiveClosure fork)
  , (mkId "forkRep", PrimitiveClosure forkRep)
  , (mkId "recv", Primitive recv)
  , (mkId "send", Primitive send)
  , (mkId "close", Primitive close)
  ]
  where
    fork :: Ctxt Value -> Value -> IO Value
    fork ctxt e@Abs{} = do
      c <- CC.newChan
      C.forkIO $
         evalIn ctxt (App nullSpan (valExpr e) (valExpr $ Chan c)) >> return ()
      return $ Pure $ valExpr $ Chan c

    forkRep :: Ctxt Value -> Value -> IO Value
    forkRep ctxt e@Abs{} = do
      c <- CC.newChan
      C.forkIO $
         evalIn ctxt (App nullSpan
                        (valExpr e)
                        (valExpr $ Promote $ valExpr $ Chan c)) >> return ()
      return $ Pure $ valExpr $ Promote $ valExpr $ Chan c
    forkRep ctxt e = error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    recv :: Value -> IO Value
    recv (Chan c) = do
      x <- CC.readChan c
      return $ Pure $ valExpr $ Constr (mkId ",") [x, Chan c]
    recv e = error $ "Bug in Granule. Trying to recevie from: " <> prettyDebug e

    send :: Value -> IO Value
    send (Chan c) = return $ Primitive
      (\v -> do
         CC.writeChan c v
         return $ Pure $ valExpr $ Chan c)
    send e = error $ "Bug in Granule. Trying to send from: " <> prettyDebug e

    close :: Value -> IO Value
    close (Chan c) = return $ Pure $ valExpr $ Constr (mkId "()") []

    cast :: Int -> Double
    cast = fromInteger . toInteger

    openFile :: Value -> IO Value
    openFile (StringLiteral s) = return $
      Primitive (\(Constr m []) ->
        let mode = (read (internalName m)) :: SIO.IOMode
        in do
             h <- SIO.openFile (unpack s) mode
             return $ Pure (Val nullSpan (Handle h)))

    hPutChar :: Value -> IO Value
    hPutChar (Handle h) = return $
      Primitive (\(CharLiteral c) -> do
         SIO.hPutChar h c
         return $ Pure (Val nullSpan (Handle h)))

    hGetChar :: Value -> IO Value
    hGetChar (Handle h) = do
          c <- SIO.hGetChar h
          return $ Pure (Val nullSpan (Constr (mkId ",") [Handle h, CharLiteral c]))

    hClose :: Value -> IO Value
    hClose (Handle h) = do
         SIO.hClose h
         return $ Pure (Val nullSpan (Constr (mkId "()") []))

evalDefs :: Ctxt Value -> [Def] -> IO (Ctxt Value)
evalDefs ctxt [] = return ctxt
evalDefs ctxt (Def _ var e [] _ : defs) = do
    val <- evalIn ctxt e
    case extend ctxt var val of
      Some ctxt -> evalDefs ctxt defs
      None msgs -> error $ unlines msgs
evalDefs ctxt (d : defs) = do
    let d' = desugar d
    evalDefs ctxt (d' : defs)

eval :: AST -> IO (Maybe Value)
eval (AST dataDecls defs) = do
    bindings <- evalDefs builtIns defs
    case lookup (mkId "main") bindings of
      Nothing -> return Nothing
      Just (Pure e)    -> fmap Just (evalIn bindings e)
      Just (Promote e) -> fmap Just (evalIn bindings e)
      Just val         -> return $ Just val
