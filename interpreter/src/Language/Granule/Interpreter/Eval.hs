-- Granule interpreter
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}


{-# options_ghc -Wno-incomplete-uni-patterns #-}

module Language.Granule.Interpreter.Eval where

import Language.Granule.Interpreter.Desugar
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Context
import Language.Granule.Utils

import Language.Granule.Syntax.Type

import Data.Text (cons, pack, uncons, unpack, snoc, unsnoc)
import qualified Data.Text.IO as Text
import Control.Monad (when, foldM)

import System.IO.Unsafe (unsafePerformIO)
import Control.Exception (catch, throwIO, IOException)
import GHC.IO.Exception (IOErrorType( OtherError ))
import qualified Control.Concurrent as C (forkIO)
import qualified Control.Concurrent.Chan as CC (newChan, writeChan, readChan, Chan)
-- import Foreign.Marshal.Alloc (free, malloc)
-- import Foreign.Ptr (castPtr)
-- import Foreign.Storable (peek, poke)
import qualified Data.Array.IO as MA
import System.IO (hFlush, stdout, stderr)
import qualified System.IO as SIO

import System.IO.Error (mkIOError)

type RValue = Value (Runtime Type) Type
type RExpr = Expr (Runtime Type) Type

-- | Runtime values only used in the interpreter
data Runtime a =
  -- | Primitive functions (builtins)
    Primitive ((Value (Runtime a) a) -> Value (Runtime a) a)

  -- | Primitive operations that also close over the context
  | PrimitiveClosure (Ctxt (Value (Runtime a) a) -> (Value (Runtime a) a) -> (Value (Runtime a) a))

  -- | File handler
  | Handle SIO.Handle

  -- | Channels
  | Chan (CC.Chan (Value (Runtime a) a))

  -- | Delayed side effects wrapper
  | PureWrapper (IO (Expr (Runtime a) a))

  -- | Mutable arrays
  | FloatArray (MA.IOArray Int Double)


diamondConstr :: IO (Expr (Runtime Type) Type) -> RValue
diamondConstr = Ext dummyType . PureWrapper

isDiaConstr :: RValue -> Maybe (IO (Expr (Runtime Type) Type))
isDiaConstr (Pure _ e) = Just $ return e
isDiaConstr (Ext _ (PureWrapper e)) = Just e
isDiaConstr _ = Nothing

instance Show (Runtime a) where
  show (Chan _) = "Some channel"
  show (Primitive _) = "Some primitive"
  show (PrimitiveClosure _) = "Some primitive closure"
  show (Handle _) = "Some handle"
  show (PureWrapper _) = "<suspended IO>"
  show (FloatArray arr) = "<array>"

instance Pretty (Runtime a) where
  pretty = show

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
    OpDiv -> case (v1, v2) of
      (NumFloat n1, NumFloat n2) -> NumFloat (n1 / n2)
      _ -> evalFail
    OpMinus -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> NumInt (n1 - n2)
      (NumFloat n1, NumFloat n2) -> NumFloat (n1 - n2)
      _ -> evalFail
    OpEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr dummyType (mkId . show $ (n1 == n2)) []
      (NumFloat n1, NumFloat n2) -> Constr dummyType (mkId . show $ (n1 == n2)) []
      _ -> evalFail
    OpNotEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr dummyType (mkId . show $ (n1 /= n2)) []
      (NumFloat n1, NumFloat n2) -> Constr dummyType (mkId . show $ (n1 /= n2)) []
      _ -> evalFail
    OpLesserEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr dummyType (mkId . show $ (n1 <= n2)) []
      (NumFloat n1, NumFloat n2) -> Constr dummyType (mkId . show $ (n1 <= n2)) []
      _ -> evalFail
    OpLesser -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr dummyType (mkId . show $ (n1 < n2)) []
      (NumFloat n1, NumFloat n2) -> Constr dummyType (mkId . show $ (n1 < n2)) []
      _ -> evalFail
    OpGreaterEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr dummyType (mkId . show $ (n1 >= n2)) []
      (NumFloat n1, NumFloat n2) -> Constr dummyType (mkId . show $ (n1 >= n2)) []
      _ -> evalFail
    OpGreater -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr dummyType (mkId . show $ (n1 > n2)) []
      (NumFloat n1, NumFloat n2) -> Constr dummyType (mkId . show $ (n1 > n2)) []
      _ -> evalFail
  where
    evalFail = error $ show [show op, show v1, show v2]

-- Needed in various places because the evaluator is not very good at preserving
-- type information (yet) TODO!
dummyType :: Type
dummyType = TyVar $ mkId "dummy"

-- Call-by-value big step semantics
evalIn :: (?globals :: Globals) => Ctxt RValue -> RExpr -> IO RValue
evalIn ctxt (App s _ _ e1 e2) = do
    -- (cf. APP_L)
    v1 <- evalIn ctxt e1
    case v1 of
      (Ext _ (Primitive k)) -> do
        -- (cf. APP_R)
        v2 <- evalIn ctxt e2
        return $ k v2

      Abs _ p _ e3 -> do
        -- CallByName extension
        if CBN `elem` globalsExtensions ?globals
          then do
            -- (cf. P_BETA CBN)
            pResult <- pmatch ctxt [(p, e3)] e2
            case pResult of
              Just e3' -> evalIn ctxt e3'
              _ -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in application at " <> pretty s

          -- CallByValue default
          else do
            -- (cf. APP_R)
            v2 <- evalIn ctxt e2
            -- (cf. P_BETA)
            pResult <- pmatch ctxt [(p, e3)] (valExpr v2)
            case pResult of
              Just e3' -> evalIn ctxt e3'
              _ -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in application at " <> pretty s

      Constr ty c vs -> do
        -- (cf. APP_R)
        v2 <- evalIn ctxt e2
        return $ Constr ty c (vs <> [v2])

      _ -> error $ show v1
      -- _ -> error "Cannot apply value"

-- Deriving applications get resolved to their names
evalIn ctxt (AppTy _ _ _ (Val s a rf (Var a' n)) t) | internalName n `elem` ["push", "pull", "copyShape", "drop"] = do
  -- Replace with a deriving variable
  evalIn ctxt (Val s a rf (Var a' (mkId $ pretty n <> "@" <> pretty t)))

-- Other type applications have no run time component (currently)
evalIn ctxt (AppTy s _ _ e t) = do
  evalIn ctxt e

evalIn ctxt (Binop _ _ _ op e1 e2) = do
     v1 <- evalIn ctxt e1
     v2 <- evalIn ctxt e2
     return $ evalBinOp op v1 v2

evalIn ctxt (LetDiamond s _ _ p _ e1 e2) = do
  -- (cf. LET_1)
  v1 <- evalIn ctxt e1
  case v1 of
    (isDiaConstr -> Just e) -> do
        -- Do the delayed side effect
        eInner <- e
        -- (cf. LET_2)
        v1' <- evalIn ctxt eInner
        -- (cf. LET_BETA)
        pResult  <- pmatch ctxt [(p, e2)] (valExpr v1')
        case pResult of
          Just e2' -> do
              evalIn ctxt e2'
          Nothing -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in let at " <> pretty s

    other -> fail $ "Runtime exception: Expecting a diamonad value but got: "
                      <> prettyDebug other

evalIn ctxt (TryCatch s _ _ e1 p _ e2 e3) = do
  v1 <- evalIn ctxt e1
  case v1 of
    (isDiaConstr -> Just e) -> do
        -- (cf. TRY_BETA_1)
      catch ( do
          eInner <- e
          e1' <- evalIn ctxt eInner
          pmatch ctxt [(PBox s dummyType False p, e2)] (valExpr e1') >>=
            \v ->
              case v of
                Just e2' -> evalIn ctxt e2'
                Nothing -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in try at " <> pretty s
        )
         -- (cf. TRY_BETA_2)
        (\(e :: IOException) -> evalIn ctxt e3)
    other -> fail $ "Runtime exception: Expecting a diamonad value but got: " <> prettyDebug other

{-
-- Hard-coded 'scale', removed for now
evalIn _ (Val _ _ _ (Var _ v)) | internalName v == "scale" = return
  (Abs () (PVar nullSpan () False $ mkId " x") Nothing (Val nullSpan () False
    (Abs () (PVar nullSpan () False $ mkId " y") Nothing (
      letBox nullSpan (PVar nullSpan () False $ mkId " ye")
         (Val nullSpan () False (Var () (mkId " y")))
         (Binop nullSpan () False
           OpTimes (Val nullSpan () False (Var () (mkId " x"))) (Val nullSpan () False (Var () (mkId " ye"))))))))
-}

evalIn ctxt (Val _ ty _ (Var _ x)) = do
    case lookup x ctxt of
      Just val@(Ext _ (PrimitiveClosure f)) -> return $ Ext ty $ Primitive (f ctxt)
      Just val -> return val
      Nothing  -> fail $ "Variable '" <> sourceName x <> "' is undefined in context."

evalIn ctxt (Val s ty _ (Promote ty' e)) = do
  -- CallByName extension
  if CBN `elem` (globalsExtensions ?globals)
    then do
      return $ Promote ty e
    else do
      -- (cf. Box)
      v <- evalIn ctxt e
      return $ Promote ty' (Val s ty' False v)

evalIn _ (Val _ _ _ v) = return v

evalIn ctxt (Case s a b guardExpr cases) = do
    v <- evalIn ctxt guardExpr
    p <- pmatch ctxt cases (Val s a b v)
    case p of
      Just ei -> evalIn ctxt ei
      Nothing             ->
        error $ "Incomplete pattern match:\n  cases: "
             <> pretty cases <> "\n  expr: " <> pretty v

evalIn ctxt (Hole _ _ _ _) = do
  error "Trying to evaluate a hole, which should not have passed the type checker."

applyBindings :: Ctxt RExpr -> RExpr -> RExpr
applyBindings [] e = e
applyBindings ((var, e'):bs) e = applyBindings bs (subst e' var e)

{-| Start pattern matching here passing in a context of values
    a list of cases (pattern-expression pairs) and the guard expression.
    If there is a matching pattern p_i then return Just of the branch
    expression e_i and a list of bindings in scope -}
pmatch ::
  (?globals :: Globals)
  => Ctxt RValue
  -> [(Pattern Type, RExpr)]
  -> RExpr
  -> IO (Maybe RExpr)
pmatch _ [] _ =
  return Nothing

pmatch _ ((PWild _ _ _, e):_)  _ =
  return $ Just e

pmatch ctxt ((PConstr _ _ _ id innerPs, t0):ps) v@(Val s a b (Constr _ id' vs))
 | id == id' && length innerPs == length vs = do

  -- Fold over the inner patterns
  let vs' = map valExpr vs
  tLastM <- foldM (\tiM (pi, vi) -> case tiM of
                                      Nothing -> return Nothing
                                      Just ti -> pmatch ctxt [(pi, ti)] vi) (Just t0) (zip innerPs vs')

  case tLastM of
    Just tLast -> return $ Just tLast
    -- There was a failure somewhere
    Nothing  -> pmatch ctxt ps v

pmatch ctxt ((PConstr s a b id innerPs, t0):ps) e =
  -- Can only happen in CBN case
  if CBN `elem` globalsExtensions ?globals
    then do
      -- Force evaluation of term
      v <- evalIn ctxt e
      pmatch ctxt ((PConstr s a b id innerPs, t0):ps) (valExpr v)
    else
      -- In CBV mode this just meands we failed to pattern match
      pmatch ctxt ps e

pmatch _ ((PVar _ _ _ var, e):_) v =
  return $ Just $ subst v var e

pmatch ctxt ((PBox _ _ _ p, e):ps) v@(Val _ _ _ (Promote _ v')) = do
  match <- pmatch ctxt [(p, e)] v'
  case match of
    Just e -> return $ Just e
    Nothing -> pmatch ctxt ps v

pmatch ctxt ((PInt _ _ _ n, e):ps) (Val _ _ _ (NumInt m)) | n == m = return $ Just e

pmatch ctxt ((PFloat _ _ _ n, e):ps) (Val _ _ _ (NumFloat m)) | n == m = return $ Just e

pmatch ctxt (_:ps) v = pmatch ctxt ps v

valExpr :: ExprFix2 g ExprF ev Type -> ExprFix2 ExprF g ev Type
valExpr = Val nullSpanNoFile (TyVar $ mkId "dummy") False

builtIns :: (?globals :: Globals) => Ctxt RValue
builtIns =
  [
    (mkId "div", Ext dummyType $ Primitive $ \(NumInt n1)
          -> Ext dummyType $ Primitive $ \(NumInt n2) -> NumInt (n1 `div` n2))
  , (mkId "use", Ext dummyType $ Primitive $ \v -> Promote dummyType (Val nullSpan dummyType False v))
  , (mkId "drop@Int", Ext dummyType $ Primitive $ \v -> (Constr dummyType (mkId "dummyType") []))
  , (mkId "drop@Char", Ext dummyType $ Primitive $ \v -> (Constr dummyType (mkId "dummyType") []))
  , (mkId "drop@Float", Ext dummyType $ Primitive $ \v -> (Constr dummyType (mkId "dummyType") []))
  , (mkId "drop@String", Ext dummyType $ Primitive $ \v -> (Constr dummyType (mkId "dummyType") []))
  , (mkId "copyShape@Int", Ext dummyType $ Primitive $ \v -> Constr dummyType (mkId ",") [v, v])
  , (mkId "copyShape@Char", Ext dummyType $ Primitive $ \v -> Constr dummyType (mkId ",") [v, v])
  , (mkId "copyShape@Float", Ext dummyType $ Primitive $ \v -> Constr dummyType (mkId ",") [v, v])
  , (mkId "copyShape@String", Ext dummyType $ Primitive $ \v -> Constr dummyType (mkId ",") [v, v])
  , (mkId "pure",       Ext dummyType $ Primitive $ \v -> Pure dummyType (Val nullSpan dummyType False v))
  , (mkId "fromPure",   Ext dummyType $ Primitive $ \(Pure _ (Val nullSpan dummyType False v)) ->  v)
  , (mkId "tick",       Pure dummyType (Val nullSpan dummyType False (Constr dummyType (mkId "dummyType") [])))
  , (mkId "intToFloat", Ext dummyType $ Primitive $ \(NumInt n) -> NumFloat (cast n))
  , (mkId "showInt",    Ext dummyType $ Primitive $ \n -> case n of
                              NumInt n -> StringLiteral . pack . show $ n
                              n        -> error $ show n)
  , (mkId "fromStdin", diamondConstr $ do
      when testing (error "trying to read stdin while testing")
      putStr "> "
      hFlush stdout
      val <- Text.getLine
      return $ Val nullSpan dummyType False (StringLiteral val))

  , (mkId "readInt", diamondConstr $ do
        when testing (error "trying to read stdin while testing")
        putStr "> "
        hFlush stdout
        val <- Text.getLine
        return $ Val nullSpan dummyType False (NumInt $ read $ unpack val))
  , (mkId "throw", diamondConstr (throwIO $ mkIOError OtherError "exc" Nothing Nothing))
  , (mkId "toStdout", Ext dummyType $ Primitive $ \(StringLiteral s) ->
                                diamondConstr (do
                                  when testing (error "trying to write `toStdout` while testing")
                                  Text.putStr s
                                  return $ (Val nullSpan dummyType False (Constr dummyType (mkId "dummyType") []))))
  , (mkId "toStderr", Ext dummyType $ Primitive $ \(StringLiteral s) ->
                                diamondConstr (do
                                  when testing (error "trying to write `toStderr` while testing")
                                  let red x = "\ESC[31;1m" <> x <> "\ESC[0m"
                                  Text.hPutStr stderr $ red s
                                  return $ Val nullSpan dummyType False (Constr dummyType (mkId "dummyType") [])))
  , (mkId "openHandle", Ext dummyType $ Primitive openHandle)
  , (mkId "readChar", Ext dummyType $ Primitive readChar)
  , (mkId "writeChar", Ext dummyType $ Primitive writeChar)
  , (mkId "closeHandle",   Ext dummyType $ Primitive closeHandle)
  , (mkId "showChar",
        Ext dummyType $ Primitive $ \(CharLiteral c) -> StringLiteral $ pack [c])
  , (mkId "charToInt",
        Ext dummyType $ Primitive $ \(CharLiteral c) -> NumInt $ fromEnum c)
  , (mkId "charFromInt",
        Ext dummyType $ Primitive $ \(NumInt c) -> CharLiteral $ toEnum c)
  , (mkId "stringAppend",
        Ext dummyType $ Primitive $ \(StringLiteral s) ->
          Ext dummyType $ Primitive $ \(StringLiteral t) -> StringLiteral $ s <> t)
  , ( mkId "stringUncons"
    , Ext dummyType $ Primitive $ \(StringLiteral s) -> case uncons s of
        Just (c, s) -> Constr dummyType (mkId "Some") [Constr dummyType (mkId ",") [CharLiteral c, StringLiteral s]]
        Nothing     -> Constr dummyType (mkId "None") []
    )
  , ( mkId "stringCons"
    , Ext dummyType $ Primitive $ \(CharLiteral c) ->
        Ext dummyType $ Primitive $ \(StringLiteral s) -> StringLiteral (cons c s)
    )
  , ( mkId "stringUnsnoc"
    , Ext dummyType $ Primitive $ \(StringLiteral s) -> case unsnoc s of
        Just (s, c) -> Constr dummyType (mkId "Some") [Constr dummyType (mkId ",") [StringLiteral s, CharLiteral c]]
        Nothing     -> Constr dummyType (mkId "None") []
    )
  , ( mkId "stringSnoc"
    , Ext dummyType $ Primitive $ \(StringLiteral s) ->
        Ext dummyType $ Primitive $ \(CharLiteral c) -> StringLiteral (snoc s c)
    )
  , (mkId "isEOF", Ext dummyType $ Primitive $ \(Ext _ (Handle h)) -> Ext dummyType $ PureWrapper $ do
        b <- SIO.isEOF
        let boolflag =
             case b of
               True -> Constr dummyType (mkId "True") []
               False -> Constr dummyType (mkId "False") []
        return . Val nullSpan dummyType False $ Constr dummyType (mkId ",") [Ext dummyType $ Handle h, boolflag])
  , (mkId "forkLinear", Ext dummyType $ PrimitiveClosure forkLinear)
  , (mkId "forkLinear'", Ext dummyType $ PrimitiveClosure forkLinear')
  , (mkId "fork",    Ext dummyType $ PrimitiveClosure forkRep)
  , (mkId "recv",    Ext dummyType $ Primitive recv)
  , (mkId "send",    Ext dummyType $ Primitive send)
  , (mkId "close",   Ext dummyType $ Primitive close)
  , (mkId "grecv",    Ext dummyType $ Primitive grecv)
  , (mkId "gsend",    Ext dummyType $ Primitive gsend)
  , (mkId "gclose",   Ext dummyType $ Primitive gclose)
  -- , (mkId "trace",   Ext dummyType $ Primitive $ \(StringLiteral s) -> diamondConstr $ do { Text.putStr s; hFlush stdout; return $ Val nullSpan dummyType False (Constr dummyType (mkId "dummyType") []) })
  -- , (mkId "newPtr", malloc)
  -- , (mkId "swapPtr", peek poke castPtr) -- hmm probably don't need to cast the Ptr
  -- , (mkId "freePtr", free)
  , (mkId "uniqueReturn",  Ext dummyType $ Primitive $ \(Promote _ (Val nullSpan _ False v)) -> Promote dummyType (Val nullSpan dummyType False v))
  , (mkId "uniqueBind",    Ext dummyType $ Primitive $ \(Promote _ (Val nullSpan _ False f)) -> Ext dummyType $ Primitive $ \(Promote _ (Val nullSpan _ False v)) -> Promote dummyType (App nullSpan dummyType False (Val nullSpan dummyType False f) (Val nullSpan dummyType False v)))
  , (mkId "newFloatArray",  Ext dummyType $ Primitive newFloatArray)
  , (mkId "lengthFloatArray",  Ext dummyType $ Primitive lengthFloatArray)
  , (mkId "readFloatArray",  Ext dummyType $ Primitive readFloatArray)
  , (mkId "writeFloatArray",  Ext dummyType $ Primitive writeFloatArray)
  ]
  where
    forkLinear :: (?globals :: Globals) => Ctxt RValue -> RValue -> RValue
    forkLinear ctxt e@Abs{} = Ext dummyType (unsafePerformIO $ do
      c <- CC.newChan
      _ <- C.forkIO $
         evalIn ctxt (App nullSpan dummyType False (valExpr e) (valExpr $ Ext dummyType $ Chan c)) >> return ()
      return $ Chan c)
    forkLinear ctxt e = error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    forkLinear' :: (?globals :: Globals) => Ctxt RValue -> RValue -> RValue
    forkLinear' ctxt e@Abs{} = Ext dummyType (unsafePerformIO $ do
      c <- CC.newChan
      _ <- C.forkIO $
         evalIn ctxt (App nullSpan dummyType False
                        (valExpr e)
                        (valExpr $ Promote dummyType $ valExpr $ Ext dummyType $ Chan c)) >> return ()
      return $ Chan c)
    forkLinear' ctxt e = error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    forkRep :: (?globals :: Globals) => Ctxt RValue -> RValue -> RValue
    forkRep ctxt e@Abs{} = diamondConstr $ do
      c <- CC.newChan
      _ <- C.forkIO $
         evalIn ctxt (App nullSpan dummyType False
                        (valExpr e)
                        (valExpr $ Promote dummyType $ valExpr $ Ext dummyType $ Chan c)) >> return ()
      return $ valExpr $ Promote dummyType $ valExpr $ Ext dummyType $ Chan c
    forkRep ctxt e = error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    recv :: (?globals :: Globals) => RValue -> RValue
    recv (Ext _ (Chan c)) = unsafePerformIO $ do
      x <- CC.readChan c
      return $ Constr dummyType (mkId ",") [x, Ext dummyType $ Chan c]
    recv e = error $ "Bug in Granule. Trying to recevie from: " <> prettyDebug e

    send :: (?globals :: Globals) => RValue -> RValue
    send (Ext _ (Chan c)) = Ext dummyType $ Primitive
      (\v -> unsafePerformIO $ do
         CC.writeChan c v
         return $ Ext dummyType $ Chan c)
    send e = error $ "Bug in Granule. Trying to send from: " <> prettyDebug e

    close :: RValue -> RValue
    close (Ext _ (Chan c)) = unsafePerformIO $ return $ Constr dummyType (mkId "dummyType") []
    close rval = error $ "Runtime exception: trying to close a value which is not a channel"

    grecv :: (?globals :: Globals) => RValue -> RValue
    grecv (Ext _ (Chan c)) = diamondConstr $ do
      x <- CC.readChan c
      return $ valExpr $ Constr dummyType (mkId ",") [x, Ext dummyType $ Chan c]
    grecv e = error $ "Bug in Granule. Trying to recevie from: " <> prettyDebug e

    gsend :: (?globals :: Globals) => RValue -> RValue
    gsend (Ext _ (Chan c)) = Ext dummyType $ Primitive
      (\v -> diamondConstr $ do
         CC.writeChan c v
         return $ valExpr $ Ext dummyType $ Chan c)
    gsend e = error $ "Bug in Granule. Trying to send from: " <> prettyDebug e

    gclose :: RValue -> RValue
    gclose (Ext _ (Chan c)) = diamondConstr $ return $ valExpr $ Constr dummyType (mkId "dummyType") []
    gclose rval = error $ "Runtime exception: trying to close a value which is not a channel"

    cast :: Int -> Double
    cast = fromInteger . toInteger

    openHandle :: RValue -> RValue
    openHandle (Constr _ m []) =
      Ext dummyType $ Primitive (\x -> diamondConstr (
        case x of
          (StringLiteral s) -> do
            h <- SIO.openFile (unpack s) mode
            return $ valExpr $ Ext dummyType $ Handle h
          rval -> error $ "Runtime exception: trying to open from a non string filename" <> show rval))
      where
        mode = case internalName m of
            "ReadMode" -> SIO.ReadMode
            "WriteMode" -> SIO.WriteMode
            "AppendMode" -> SIO.AppendMode
            "ReadWriteMode" -> SIO.ReadWriteMode
            x -> error $ show x

    openHandle x = error $ "Runtime exception: trying to open with a non-mode value" <> show x

    writeChar :: RValue -> RValue
    writeChar (Ext _ (Handle h)) =
      Ext dummyType $ Primitive (\c -> diamondConstr (
        case c of
          (CharLiteral c) -> do
            SIO.hPutChar h c
            return $ valExpr $ Ext dummyType $ Handle h
          _ -> error $ "Runtime exception: trying to put a non character value"))
    writeChar _ = error $ "Runtime exception: trying to put from a non handle value"

    readChar :: RValue -> RValue
    readChar (Ext _ (Handle h)) = diamondConstr $ do
          c <- SIO.hGetChar h
          return $ valExpr (Constr dummyType (mkId ",") [Ext dummyType $ Handle h, CharLiteral c])
    readChar h = error $ "Runtime exception: trying to get from a non handle value" <> prettyDebug h

    closeHandle :: RValue -> RValue
    closeHandle (Ext _ (Handle h)) = diamondConstr $ do
         SIO.hClose h
         return $ valExpr (Constr dummyType (mkId "dummyType") [])
    closeHandle _ = error $ "Runtime exception: trying to close a non handle value"

    {-# NOINLINE newFloatArray #-}
    newFloatArray :: RValue -> RValue
    newFloatArray = \(NumInt i) -> Promote dummyType (Val nullSpan dummyType False $ Ext dummyType $ FloatArray (unsafePerformIO (MA.newArray_ (0,i))))

    {-# NOINLINE readFloatArray #-}
    readFloatArray :: RValue -> RValue
    readFloatArray = \(Promote _ (Val _ _ _ (Ext _ (FloatArray arr)))) -> Ext dummyType $ Primitive $ \(NumInt i) ->
      unsafePerformIO $ do e <- MA.readArray arr i
                           return (Constr dummyType (mkId ",") [NumFloat e, Promote dummyType (Val nullSpan dummyType False $ Ext dummyType (FloatArray arr))])

    lengthFloatArray :: RValue -> RValue
    lengthFloatArray = \(Promote _ (Val _ _ _ (Ext _ (FloatArray arr)))) -> Ext dummyType $ Primitive $ \(NumInt i) ->
      unsafePerformIO $ do (_,end) <- MA.getBounds arr
                           return (Constr dummyType (mkId ",") [NumInt end, Promote dummyType (Val nullSpan dummyType False $ Ext dummyType $ FloatArray arr)])

    {-# NOINLINE writeFloatArray #-}
    writeFloatArray :: RValue -> RValue
    writeFloatArray = \(Promote _ (Val _ _ _ (Ext _ (FloatArray arr)))) ->
      Ext dummyType $ Primitive $ \(NumInt i) ->
      Ext dummyType $ Primitive $ \(NumFloat v) ->
      Promote dummyType (Val nullSpan dummyType False $ Ext dummyType $ FloatArray $ unsafePerformIO (do _ <- MA.writeArray arr i v; return arr))

evalDefs :: (?globals :: Globals) => Ctxt RValue -> [Def (Runtime Type) Type] -> IO (Ctxt RValue)
evalDefs ctxt [] = return ctxt
evalDefs ctxt (Def _ var _ (EquationList _ _ _ [Equation _ _ _ rf [] e]) _ : defs) = do
    val <- evalIn ctxt e
    case extend ctxt var val of
      Just ctxt -> evalDefs ctxt defs
      Nothing -> error $ "Name clash: `" <> sourceName var <> "` was already in the context."
evalDefs ctxt (d : defs) = do
    let d' = desugar d
    evalDefs ctxt (d' : defs)

-- Maps an AST from the parser into the interpreter version with runtime values
class RuntimeRep t where
  toRuntimeRep :: t () Type -> t (Runtime Type) Type

instance RuntimeRep Def where
  toRuntimeRep (Def s i rf eqs tys) = Def s i rf (toRuntimeRep eqs) tys

instance RuntimeRep EquationList where
  toRuntimeRep (EquationList s i rf eqns) = EquationList s i rf (map toRuntimeRep eqns)

instance RuntimeRep Equation where
  toRuntimeRep (Equation s name a rf ps e) = Equation s name a rf ps (toRuntimeRep e)

instance RuntimeRep Expr where
  toRuntimeRep (Val s a rf v) = Val s a rf (toRuntimeRep v)
  toRuntimeRep (App s a rf e1 e2) = App s a rf (toRuntimeRep e1) (toRuntimeRep e2)
  toRuntimeRep (AppTy s a rf e1 t) = AppTy s a rf (toRuntimeRep e1) t
  toRuntimeRep (Binop s a rf o e1 e2) = Binop s a rf o (toRuntimeRep e1) (toRuntimeRep e2)
  toRuntimeRep (LetDiamond s a rf p t e1 e2) = LetDiamond s a rf p t (toRuntimeRep e1) (toRuntimeRep e2)
  toRuntimeRep (TryCatch s a rf e1 p t e2 e3) = TryCatch s a rf (toRuntimeRep e1) p t (toRuntimeRep e2) (toRuntimeRep e3)
  toRuntimeRep (Case s a rf e ps) = Case s a rf (toRuntimeRep e) (map (\(p, e) -> (p, toRuntimeRep e)) ps)
  toRuntimeRep (Hole s a rf vs) = Hole s a rf vs

instance RuntimeRep Value where
  toRuntimeRep (Ext a ()) = error "Bug: Parser generated an extended value case when it shouldn't have"
  toRuntimeRep (Abs a p t e) = Abs a p t (toRuntimeRep e)
  toRuntimeRep (Promote a e) = Promote a (toRuntimeRep e)
  toRuntimeRep (Pure a e) = Pure a (toRuntimeRep e)
  toRuntimeRep (Constr a i vs) = Constr a i (map toRuntimeRep vs)
  -- identity cases
  toRuntimeRep (CharLiteral c) = CharLiteral c
  toRuntimeRep (StringLiteral c) = StringLiteral c
  toRuntimeRep (Var a x) = Var a x
  toRuntimeRep (NumInt x) = NumInt x
  toRuntimeRep (NumFloat x) = NumFloat x

eval :: (?globals :: Globals) => AST () Type -> IO (Maybe RValue)
eval (AST dataDecls defs _ _ _) = do
    bindings <- evalDefs builtIns (map toRuntimeRep defs)
    case lookup (mkId entryPoint) bindings of
      Nothing -> return Nothing
      -- Evaluate inside a promotion of pure if its at the top-level
      Just (Pure _ e)    -> fmap Just (evalIn bindings e)
      Just (Ext _ (PureWrapper e)) -> do
        eExpr <- e
        fmap Just (evalIn bindings eExpr)
      Just (Promote _ e) -> fmap Just (evalIn bindings e)
      -- ... or a regular value came out of the interpreter
      Just val           -> return $ Just val
