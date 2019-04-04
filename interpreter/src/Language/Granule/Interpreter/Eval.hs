-- Granule interpreter
{-# LANGUAGE ImplicitParams #-}

{-# options_ghc -Wno-incomplete-uni-patterns #-}

module Language.Granule.Interpreter.Eval where

import Language.Granule.Interpreter.Desugar
import Language.Granule.Interpreter.Type
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Context
import Language.Granule.Utils

import Data.Text (cons, pack, uncons, unpack, snoc, unsnoc)
import qualified Data.Text.IO as Text
import Control.Monad (when, zipWithM)
import Control.Monad.IO.Class (liftIO)

import qualified Control.Concurrent as C (forkIO)
import qualified Control.Concurrent.Chan as CC (newChan, writeChan, readChan)

import qualified System.IO as SIO


------------------------------
----- Bulk of evaluation -----
------------------------------


evalBinOp :: Operator -> RValue -> RValue -> RValue
evalBinOp op v1 v2 = case op of
    OpPlus -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> NumInt (n1 + n2)
      (NumFloat n1, NumFloat n2) -> NumFloat (n1 + n2)
      _ -> evalFail
    OpTimes -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> NumInt (n1 * n2)
      (NumFloat n1, NumFloat n2) -> NumFloat (n1 * n2)
      _ -> evalFail
    OpMinus -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> NumInt (n1 - n2)
      (NumFloat n1, NumFloat n2) -> NumFloat (n1 - n2)
      _ -> evalFail
    OpEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ (n1 == n2)) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ (n1 == n2)) []
      _ -> evalFail
    OpNotEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ (n1 /= n2)) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ (n1 /= n2)) []
      _ -> evalFail
    OpLesserEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ (n1 <= n2)) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ (n1 <= n2)) []
      _ -> evalFail
    OpLesser -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ (n1 < n2)) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ (n1 < n2)) []
      _ -> evalFail
    OpGreaterEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ (n1 >= n2)) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ (n1 >= n2)) []
      _ -> evalFail
    OpGreater -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ (n1 > n2)) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ (n1 > n2)) []
      _ -> evalFail
  where
    evalFail = error $ show [show op, show v1, show v2]


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

evalExpr (Val s _ (Var _ v)) | internalName v == "fromStdin" = do
    when testing (error "trying to read `fromStdin` while testing")
    writeStr "> "
    flushStdout
    val <- liftIO Text.getLine
    return $ Pure () (Val s () (StringLiteral val))

-- evalExpr _ (Val s _ (Var _ v)) | internalName v == "readInt" = do
--     when testing (error "trying to `readInt` while testing")
--     writeStr "> "
--     flushStdout
--     val <- liftIO readLn
--     return $ Pure () (Val s () (NumInt val))

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
       other -> fail $ "Runtime exception: Expecting a diamonad value but got: "
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

valExpr :: ExprFix2 g ExprF ev () -> ExprFix2 ExprF g ev ()
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
  , (mkId "toStdout", Ext () $ Primitive $ \(StringLiteral s) -> do
                              when testing (error "trying to write `toStdout` while testing")
                              Text.putStr s
                              return $ Pure () (Val nullSpan () (Constr () (mkId "()") [])))
  , (mkId "toStderr", Ext () $ Primitive $ \(StringLiteral s) -> do
                              when testing (error "trying to write `toStderr` while testing")
                              let red x = "\ESC[31;1m" <> x <> "\ESC[0m"
                              Text.hPutStr SIO.stderr $ red s
                              return $ Pure () (Val nullSpan () (Constr () (mkId "()") [])))
  , (mkId "openHandle", Ext () $ Primitive openHandle)
  , (mkId "readChar", Ext () $ Primitive readChar)
  , (mkId "writeChar", Ext () $ Primitive writeChar)
  , (mkId "closeHandle",   Ext () $ Primitive closeHandle)
  , (mkId "showChar",
        Ext () $ Primitive $ \(CharLiteral c) -> return $ StringLiteral $ pack [c])
  , (mkId "charToInt",
        Ext () $ Primitive $ \(CharLiteral c) -> return $ NumInt $ fromEnum c)
  , (mkId "charFromInt",
        Ext () $ Primitive $ \(NumInt c) -> return $ CharLiteral $ toEnum c)
  , (mkId "stringAppend",
        Ext () $ Primitive $ \(StringLiteral s) -> return $
          Ext () $ Primitive $ \(StringLiteral t) -> return $ StringLiteral $ s <> t)
  , ( mkId "stringUncons"
    , Ext () $ Primitive $ \(StringLiteral s) -> case uncons s of
        Just (c, s) -> return $ Constr () (mkId "Some") [Constr () (mkId ",") [CharLiteral c, StringLiteral s]]
        Nothing     -> return $ Constr () (mkId "None") []
    )
  , ( mkId "stringCons"
    , Ext () $ Primitive $ \(CharLiteral c) -> return $
        Ext () $ Primitive $ \(StringLiteral s) -> return $ StringLiteral (cons c s)
    )
  , ( mkId "stringUnsnoc"
    , Ext () $ Primitive $ \(StringLiteral s) -> case unsnoc s of
        Just (s, c) -> return $ Constr () (mkId "Some") [Constr () (mkId ",") [StringLiteral s, CharLiteral c]]
        Nothing     -> return $ Constr () (mkId "None") []
    )
  , ( mkId "stringSnoc"
    , Ext () $ Primitive $ \(StringLiteral s) -> return $
        Ext () $ Primitive $ \(CharLiteral c) -> return $ StringLiteral (snoc s c)
    )
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
      _ <- C.forkIO $
         runWithContext ctxt $ evalExpr (App nullSpan () (valExpr e) (valExpr $ Ext () $ Chan c)) >> pure ()
      return $ Pure () $ valExpr $ Ext () $ Chan c
    fork _ e = error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    forkRep :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    forkRep ctxt e@Abs{} = do
      c <- CC.newChan
      _ <- C.forkIO $ runWithContext ctxt $
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

    openHandle :: RValue -> IO RValue
    openHandle (Constr _ m []) = return $
      Ext () $ Primitive (\x ->
        case x of
          (StringLiteral s) -> do
            h <- SIO.openFile (unpack s) mode
            return $ Pure () $ valExpr $ Ext () $ Handle h
          rval -> error $ "Runtime exception: trying to open from a non string filename" <> show rval)
      where
        mode = case internalName m of
            "ReadMode" -> SIO.ReadMode
            "WriteMode" -> SIO.WriteMode
            "AppendMode" -> SIO.AppendMode
            "ReadWriteMode" -> SIO.ReadWriteMode
            x -> error $ show x

    openHandle x = error $ "Runtime exception: trying to open with a non-mode value" <> show x

    writeChar :: RValue -> IO RValue
    writeChar (Ext _ (Handle h)) = return $
      Ext () $ Primitive (\c ->
        case c of
          (CharLiteral c) -> do
            SIO.hPutChar h c
            return $ Pure () $ valExpr $ Ext () $ Handle h
          _ -> error $ "Runtime exception: trying to put a non character value")
    writeChar _ = error $ "Runtime exception: trying to put from a non handle value"

    readChar :: RValue -> IO RValue
    readChar (Ext _ (Handle h)) = do
          c <- SIO.hGetChar h
          return $ Pure () $ valExpr (Constr () (mkId ",") [Ext () $ Handle h, CharLiteral c])
    readChar _ = error $ "Runtime exception: trying to get from a non handle value"

    closeHandle :: RValue -> IO RValue
    closeHandle (Ext _ (Handle h)) = do
         SIO.hClose h
         return $ Pure () $ valExpr (Constr () (mkId "()") [])
    closeHandle _ = error $ "Runtime exception: trying to close a non handle value"

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
        Just ctxt' -> putContext ctxt' >> pure val
        Nothing -> error $ "could not extend context in definition evaluation"
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
eval (AST dataDecls defs ifaces insts _) = execEvaluator (do
    evalDefs (map toRuntimeRep defs)
    bindings <- getCurrentContext
    case lookup (mkId "main") bindings of
      Nothing -> return Nothing
      -- Evaluate inside a promotion of pure if its at the top-level
      Just (Pure _ e)    -> fmap Just (evalExpr e)
      Just (Promote _ e) -> fmap Just (evalExpr e)
      -- ... or a regular value came out of the interpreter
      Just val           -> return $ Just val) (initStateWithContext builtIns)
