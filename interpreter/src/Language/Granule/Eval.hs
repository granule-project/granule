-- Granule interpreter
{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Eval where

import Language.Granule.Desugar
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Context
import Language.Granule.Utils

import Data.Text (pack, unpack, append)
import qualified Data.Text.IO as Text
import Control.Monad (zipWithM)
import Control.Monad.IO.Class (liftIO)

import qualified Control.Concurrent as C (forkIO)
import qualified Control.Concurrent.Chan as CC (newChan, writeChan, readChan)

import qualified System.IO as SIO (hGetChar, hPutChar, hClose, openFile, IOMode, isEOF)

import Language.Granule.Eval.Type


------------------------------
----- Bulk of evaluation -----
------------------------------


evalBinOp :: String -> RValue -> RValue -> RValue
evalBinOp "+" (NumInt n1) (NumInt n2) = NumInt (n1 + n2)
evalBinOp "*" (NumInt n1) (NumInt n2) = NumInt (n1 * n2)
evalBinOp "-" (NumInt n1) (NumInt n2) = NumInt (n1 - n2)
evalBinOp "+" (NumFloat n1) (NumFloat n2) = NumFloat (n1 + n2)
evalBinOp "*" (NumFloat n1) (NumFloat n2) = NumFloat (n1 * n2)
evalBinOp "-" (NumFloat n1) (NumFloat n2) = NumFloat (n1 - n2)
evalBinOp "≡" (NumInt n) (NumInt m) = Constr () (mkId . show $ (n == m)) []
evalBinOp "≤" (NumInt n) (NumInt m) = Constr () (mkId . show $ (n <= m)) []
evalBinOp "<" (NumInt n) (NumInt m)  = Constr () (mkId . show $ (n < m)) []
evalBinOp "≥" (NumInt n) (NumInt m) = Constr () (mkId . show $ (n >= m)) []
evalBinOp ">" (NumInt n) (NumInt m)  = Constr () (mkId . show $ (n > m)) []
evalBinOp "≡" (NumFloat n) (NumFloat m) = Constr () (mkId . show $ (n == m)) []
evalBinOp "≤" (NumFloat n) (NumFloat m) = Constr () (mkId . show $ (n <= m)) []
evalBinOp "<" (NumFloat n) (NumFloat m)  = Constr () (mkId . show $ (n < m)) []
evalBinOp ">" (NumFloat n) (NumFloat m)  = Constr () (mkId . show $ (n > m)) []
evalBinOp "≥" (NumFloat n) (NumFloat m) = Constr () (mkId . show $ (n >= m)) []
evalBinOp op v1 v2 = error $ "Unknown operator " <> op
                             <> " on " <> show v1 <> " and " <> show v2


-- Call-by-value big step semantics
evalExpr :: (?globals :: Globals) => RExpr -> Evaluator RValue

evalExpr (Val s _ (Var _ v)) | internalName v == "read" = do
    writeStr "> "
    flushStdout
    val <- liftIO Text.getLine
    return $ Pure () (Val s () (StringLiteral val))

evalExpr (Val s _ (Var _ v)) | internalName v == "readInt" = do
    writeStr "> "
    flushStdout
    val <- liftIO readLn
    return $ Pure () (Val s () (NumInt val))

evalExpr (Val _ _ (Abs _ p t e)) = return $ Abs () p t e

evalExpr (App s _ e1 e2) = do
    v1 <- evalExpr e1
    case v1 of
      (Ext _ (Primitive k)) -> do
        v2 <- evalExpr e2
        runPrimitive k v2

      Abs _ p _ e3 -> do
        p <- pmatchTop [(p, e3)] e2
        case p of
          Just (e3, bindings) -> evalExpr (applyBindings bindings e3)
          _ -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in application at " <> pretty s

      Constr _ c vs -> do
        v2 <- evalExpr e2
        return $ Constr () c (vs <> [v2])

      _ -> error $ show v1
      -- _ -> error "Cannot apply value"

evalExpr (Binop _ _ op e1 e2) = do
     v1 <- evalExpr e1
     v2 <- evalExpr e2
     return $ evalBinOp op v1 v2

evalExpr (LetDiamond s _ p _ e1 e2) = do
     v1 <- evalExpr e1
     case v1 of
       Pure _ e -> do
         v1' <- evalExpr e
         p  <- pmatch [(p, e2)] v1'
         case p of
           Just (e2, bindings) -> evalExpr (applyBindings bindings e2)
           Nothing -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in let at " <> pretty s
       other -> fail $ "Runtime exception: Expecting a diamonad value bug got: "
                      <> prettyDebug other

{-
-- Hard-coded 'scale', removed for now


evalExpr (Val _ (Var v)) | internalName v == "scale" = return
  (Abs (PVar nullSpan $ mkId " x") Nothing (Val nullSpan
    (Abs (PVar nullSpan $ mkId " y") Nothing (
      letBox nullSpan (PVar nullSpan $ mkId " ye")
         (Val nullSpan (Var (mkId " y")))
         (Binop nullSpan
           "*" (Val nullSpan (Var (mkId " x"))) (Val nullSpan (Var (mkId " ye"))))))))
-}

evalExpr (Val _ _ (Var _ x)) = do
  maybeVal <- tryResolveVarOrEvalTLD x
  case maybeVal of
      Just val@(Ext _ (PrimitiveClosure f)) ->
        fmap (Ext () . Primitive . f) getCurrentContext
      Just val -> return val
      Nothing  -> fail $ "Variable '" <> sourceName x <> "' is undefined in context."

evalExpr (Val s _ (Pure _ e)) = do
  v <- evalExpr e
  return $ Pure () (Val s () v)

evalExpr (Val _ _ v) = return v

evalExpr (Case _ _ guardExpr cases) = do
    p <- pmatchTop cases guardExpr
    case p of
      Just (ei, bindings) -> evalExpr (applyBindings bindings ei)
      Nothing             ->
        error $ "Incomplete pattern match:\n  cases: "
             <> pretty cases <> "\n  expr: " <> pretty guardExpr

applyBindings :: Ctxt RExpr -> RExpr -> RExpr
applyBindings [] e = e
applyBindings ((var, e'):bs) e = applyBindings bs (subst e' var e)

{-| Start pattern matching here passing in a context of values
    a list of cases (pattern-expression pairs) and the guard expression.
    If there is a matching pattern p_i then return Just of the branch
    expression e_i and a list of bindings in scope -}
pmatchTop ::
  (?globals :: Globals)
  => [(Pattern (), RExpr)]
  -> RExpr
  -> Evaluator (Maybe (RExpr, Ctxt RExpr))

pmatchTop ((PBox _ _ (PVar _ _ var), branchExpr):_) guardExpr = do
  Promote _ e <- evalExpr guardExpr
  return (Just (subst e var branchExpr, []))

pmatchTop ((PBox _ _ (PWild _ _), branchExpr):_) guardExpr = do
  Promote _ _ <- evalExpr guardExpr
  return (Just (branchExpr, []))

pmatchTop ps guardExpr = do
  val <- evalExpr guardExpr
  pmatch ps val

pmatch ::
  (?globals :: Globals)
  => [(Pattern (), RExpr)]
  -> RValue
  -> Evaluator (Maybe (RExpr, Ctxt RExpr))
pmatch [] _ =
   return Nothing

pmatch ((PWild _ _, e):_)  _ =
   return $ Just (e, [])

pmatch ((PConstr _ _ s innerPs, e):ps) (Constr _ s' vs) | s == s' = do
   matches <- zipWithM (\p v -> pmatch [(p, e)] v) innerPs vs
   case sequence matches of
     Just ebindings -> return $ Just (e, concat $ map snd ebindings)
     Nothing        -> pmatch ps (Constr () s' vs)

pmatch ((PVar _ _ var, e):_) val =
   return $ Just (e, [(var, Val nullSpan () val)])

pmatch ((PBox _ _ p, e):ps) (Promote _ e') = do
  v <- evalExpr e'
  match <- pmatch [(p, e)] v
  case match of
    Just (_, bindings) -> return $ Just (e, bindings)
    Nothing -> pmatch ps (Promote () e')

pmatch ((PInt _ _ n, e):_)   (NumInt m)   | n == m  =
   return $ Just (e, [])

pmatch ((PFloat _ _ n, e):_) (NumFloat m) | n == m =
   return $ Just (e, [])

pmatch (_:ps) val = pmatch ps val

valExpr = Val nullSpanNoFile ()

builtIns :: (?globals :: Globals) => Ctxt RValue
builtIns =
  [
    (mkId "div", Ext () $ Primitive $ \(NumInt n1)
          -> return $ Ext () $ Primitive $ \(NumInt n2) ->
              return $ NumInt (n1 `div` n2))
  , (mkId "pure",       Ext () $ Primitive $ \v -> return $ Pure () (Val nullSpan () v))
  , (mkId "intToFloat", Ext () $ Primitive $ \(NumInt n) -> return $ NumFloat (cast n))
  , (mkId "showInt",    Ext () $ Primitive $ \n -> case n of
                              NumInt n -> return . StringLiteral . pack . show $ n
                              n        -> error $ show n)
  , (mkId "write", Ext () $ Primitive $ \(StringLiteral s) -> do
                              Text.putStrLn s
                              return $ Pure () (Val nullSpan () (Constr () (mkId "()") [])))
  , (mkId "openFile", Ext () $ Primitive openFile)
  , (mkId "hGetChar", Ext () $ Primitive hGetChar)
  , (mkId "hPutChar", Ext () $ Primitive hPutChar)
  , (mkId "hClose",   Ext () $ Primitive hClose)
  , (mkId "showChar",
        Ext () $ Primitive $ \(CharLiteral c) -> return $ StringLiteral $ pack [c])
  , (mkId "stringAppend",
        Ext () $ Primitive $ \(StringLiteral s) -> return $
          Ext () $ Primitive $ \(StringLiteral t) -> return $ StringLiteral $ s `append` t)
  , (mkId "isEOF", Ext () $ Primitive $ \(Ext _ (Handle h)) -> do
        b <- SIO.isEOF
        let boolflag =
             case b of
               True -> Constr () (mkId "True") []
               False -> Constr () (mkId "False") []
        return . (Pure ()) . Val nullSpan () $ Constr () (mkId ",") [Ext () $ Handle h, boolflag])
  , (mkId "fork",    Ext () $ PrimitiveClosure fork)
  , (mkId "forkRep", Ext () $ PrimitiveClosure forkRep)
  , (mkId "forkC", Ext () $ PrimitiveClosure forkRep)
  , (mkId "recv",    Ext () $ Primitive recv)
  , (mkId "send",    Ext () $ Primitive send)
  , (mkId "close",   Ext () $ Primitive close)
  ]
  where
    fork :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    fork ctxt e@Abs{} = do
      c <- CC.newChan
      C.forkIO $
         runWithContext ctxt $ evalExpr (App nullSpan () (valExpr e) (valExpr $ Ext () $ Chan c)) >> pure ()
      return $ Pure () $ valExpr $ Ext () $ Chan c
    fork _ e = error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    forkRep :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    forkRep ctxt e@Abs{} = do
      c <- CC.newChan
      C.forkIO $ runWithContext ctxt $
         evalExpr (App nullSpan ()
                   (valExpr e)
                   (valExpr $ Promote () $ valExpr $ Ext () $ Chan c)) >> return ()
      return $ Pure () $ valExpr $ Promote () $ valExpr $ Ext () $ Chan c
    forkRep _ e = error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    recv :: (?globals :: Globals) => RValue -> IO RValue
    recv (Ext _ (Chan c)) = do
      x <- CC.readChan c
      return $ Pure () $ valExpr $ Constr () (mkId ",") [x, Ext () $ Chan c]
    recv e = error $ "Bug in Granule. Trying to recevie from: " <> prettyDebug e

    send :: (?globals :: Globals) => RValue -> IO RValue
    send (Ext _ (Chan c)) = return $ Ext () $ Primitive
      (\v -> do
         CC.writeChan c v
         return $ Pure () $ valExpr $ Ext () $ Chan c)
    send e = error $ "Bug in Granule. Trying to send from: " <> prettyDebug e

    close :: RValue -> IO RValue
    close (Ext _ (Chan c)) = return $ Pure () $ valExpr $ Constr () (mkId "()") []
    close rval = error $ "Runtime exception: trying to close a value which is not a channel"

    cast :: Int -> Double
    cast = fromInteger . toInteger

    openFile :: RValue -> IO RValue
    openFile (StringLiteral s) = return $
      Ext () $ Primitive (\x ->
        case x of
           (Constr _ m []) -> do
               let mode = (read (internalName m)) :: SIO.IOMode
               h <- SIO.openFile (unpack s) mode
               return $ Pure () $ valExpr $ Ext () $ Handle h
           rval -> error $ "Runtime exception: trying to open with a non-mode value")
    openFile _ = error $ "Runtime exception: trying to open from a non string filename"

    hPutChar :: RValue -> IO RValue
    hPutChar (Ext _ (Handle h)) = return $
      Ext () $ Primitive (\c ->
        case c of
          (CharLiteral c) -> do
            SIO.hPutChar h c
            return $ Pure () $ valExpr $ Ext () $ Handle h
          _ -> error $ "Runtime exception: trying to put a non character value")
    hPutChar _ = error $ "Runtime exception: trying to put from a non handle value"

    hGetChar :: RValue -> IO RValue
    hGetChar (Ext _ (Handle h)) = do
          c <- SIO.hGetChar h
          return $ Pure () $ valExpr (Constr () (mkId ",") [Ext () $ Handle h, CharLiteral c])
    hGetChar _ = error $ "Runtime exception: trying to get from a non handle value"

    hClose :: RValue -> IO RValue
    hClose (Ext _ (Handle h)) = do
         SIO.hClose h
         return $ Pure () $ valExpr (Constr () (mkId "()") [])
    hClose _ = error $ "Runtime exception: trying to close a non handle value"

evalDefs :: (?globals :: Globals) => [Def (Runtime ()) ()] -> Evaluator ()
evalDefs defs = do
  let desugared = fmap desugarDef defs
  buildDefMap desugared
  mapM_ evalDef desugared
  where desugarDef def@(Def _ _ [Equation _ _ [] _] _) = def
        desugarDef def = desugar def


evalDef :: (?globals :: Globals) => Def (Runtime ()) () -> Evaluator RValue
evalDef (Def _ var [Equation _ _ [] e] _) = do
  existing <- lookupInCurrentContext var
  case existing of
    -- we've already evaluated this definition
    Just v -> pure v
    Nothing -> do
      val <- evalExpr e
      ctxt <- getCurrentContext
      case extend ctxt var val of
        Some ctxt' -> putContext ctxt' >> pure val
        None msgs -> error $ unlines msgs
evalDef _ = fail "received a non-desugared definition in evaluation"


tryResolveVarOrEvalTLD :: (?globals :: Globals) => Id -> Evaluator (Maybe RValue)
tryResolveVarOrEvalTLD n = do
  maybeVal <- lookupInCurrentContext n
  case maybeVal of
    Just v -> pure . pure $ v
    Nothing -> do
      -- if we can't find an already-evaluated name, then
      -- try and find a TLD with the given name, and evaluate it
      def <- lookupInDefMap n
      maybe (pure Nothing) (fmap Just . evalDef) def


eval :: (?globals :: Globals) => AST () () -> IO (Maybe RValue)
eval (AST dataDecls defs ifaces insts) = execEvaluator (do
    evalDefs (map toRuntimeRep defs)
    bindings <- getCurrentContext
    case lookup (mkId "main") bindings of
      Nothing -> return Nothing
      -- Evaluate inside a promotion of pure if its at the top-level
      Just (Pure _ e)    -> fmap Just (evalExpr e)
      Just (Promote _ e) -> fmap Just (evalExpr e)
      -- ... or a regular value came out of the interpreter
      Just val           -> return $ Just val) (initStateWithContext builtIns)
