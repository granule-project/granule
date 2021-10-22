-- Granule interpreter
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

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
import Data.Bifunctor

type RValue = Value (Runtime ()) ()
type RExpr = Expr (Runtime ()) ()

-- | Runtime values only used in the interpreter
data Runtime a =
  -- | Primitive functions (builtins)
    Primitive (Value (Runtime a) a -> Value (Runtime a) a)

  -- | Primitive operations that also close over the context
  | PrimitiveClosure (Ctxt (Value (Runtime a) a) -> Value (Runtime a) a -> Value (Runtime a) a)

  -- | File handler
  | Handle SIO.Handle

  -- | Channels
  | Chan (CC.Chan (Value (Runtime a) a))

  -- | Delayed side effects wrapper
  | PureWrapper (IO (Expr (Runtime a) ()))

  -- | Mutable arrays
  | FloatArray (MA.IOArray Int Double)


diamondConstr :: IO (Expr (Runtime ()) ()) -> RValue
diamondConstr = Ext () . PureWrapper

isDiaConstr :: RValue -> Maybe (IO (Expr (Runtime ()) ()))
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
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ n1 == n2) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ n1 == n2) []
      _ -> evalFail
    OpNotEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ n1 /= n2) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ n1 /= n2) []
      _ -> evalFail
    OpLesserEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ n1 <= n2) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ n1 <= n2) []
      _ -> evalFail
    OpLesser -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ n1 < n2) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ n1 < n2) []
      _ -> evalFail
    OpGreaterEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ n1 >= n2) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ n1 >= n2) []
      _ -> evalFail
    OpGreater -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ n1 > n2) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ n1 > n2) []
      _ -> evalFail
  where
    evalFail = error $ show [show op, show v1, show v2]

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

      Constr _ c vs -> do
        -- (cf. APP_R)
        v2 <- evalIn ctxt e2
        return $ Constr () c (vs <> [v2])

      _ -> error $ show v1
      -- _ -> error "Cannot apply value"

-- Deriving applications get resolved to their names
evalIn ctxt (AppTy _ _ _ (Val s a rf (Var a' n)) t) | internalName n `elem` ["push", "pull", "copyShape", "drop"] =
  evalIn ctxt (Val s a rf (Var a' (mkId $ pretty n <> "@" <> pretty t)))

-- Other type applications have no run time component (currently)
evalIn ctxt (AppTy s _ _ e t) =
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
          Just e2' ->
              evalIn ctxt e2'
          Nothing -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in let at " <> pretty s

    other -> fail $ "Runtime exception: Expecting a diamonad value but got: "
                      <> prettyDebug other

evalIn ctxt (TryCatch s _ _ e1 p _ e2 e3) = do
  v1 <- evalIn ctxt e1
  case v1 of
    (isDiaConstr -> Just e) ->
      catch ( do
        eInner <- e
        e1' <- evalIn ctxt eInner
        pmatch ctxt [(PBox s () False p, e2)] (valExpr e1') >>=
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

evalIn ctxt (Val _ _ _ (Var _ x)) =
    case lookup x ctxt of
      Just val@(Ext _ (PrimitiveClosure f)) -> return $ Ext () $ Primitive (f ctxt)
      Just val -> return val
      Nothing  -> fail $ "Variable '" <> sourceName x <> "' is undefined in context."

evalIn ctxt (Val s _ _ (Promote _ e)) =
  if CBN `elem` (globalsExtensions ?globals)
    then do
      return $ Promote () e
    else do
      -- (cf. Box)
      v <- evalIn ctxt e
      return $ Promote () (Val s () False v)

evalIn ctxt (Val s _ _ (Nec _ e)) =
  if CBN `elem` (globalsExtensions ?globals)
    then do
      return $ Nec () e
    else do
      v <- evalIn ctxt e
      return $ Nec () (Val s () False v)

evalIn _ (Val _ _ _ v) = return v

evalIn ctxt (Case s a b guardExpr cases) = do
    v <- evalIn ctxt guardExpr
    p <- pmatch ctxt cases (Val s a b v)
    case p of
      Just ei -> evalIn ctxt ei
      Nothing             ->
        error $ "Incomplete pattern match:\n  cases: "
             <> pretty cases <> "\n  expr: " <> pretty v

evalIn ctxt (Hole {}) =
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
  -> [(Pattern (), RExpr)]
  -> RExpr
  -> IO (Maybe RExpr)
pmatch _ [] _ =
  return Nothing

pmatch _ ((PWild {}, e):_)  _ =
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

valExpr :: ExprFix2 g ExprF ev () -> ExprFix2 ExprF g ev ()
valExpr = Val nullSpanNoFile () False

builtIns :: (?globals :: Globals) => Ctxt RValue
{-# NOINLINE builtIns #-}
builtIns =
  [
    (mkId "div", Ext () $ Primitive $ \(NumInt n1)
          -> Ext () $ Primitive $ \(NumInt n2) -> NumInt (n1 `div` n2))
  , (mkId "use", Ext () $ Primitive $ \v -> Promote () (Val nullSpan () False v))
  , (mkId "drop@Int", Ext () $ Primitive $ \v -> (Constr () (mkId "()") []))
  , (mkId "drop@Char", Ext () $ Primitive $ \v -> (Constr () (mkId "()") []))
  , (mkId "drop@Float", Ext () $ Primitive $ \v -> (Constr () (mkId "()") []))
  , (mkId "drop@String", Ext () $ Primitive $ \v -> (Constr () (mkId "()") []))
  , (mkId "copyShape@Int", Ext () $ Primitive $ \v -> Constr () (mkId ",") [v, v])
  , (mkId "copyShape@Char", Ext () $ Primitive $ \v -> Constr () (mkId ",") [v, v])
  , (mkId "copyShape@Float", Ext () $ Primitive $ \v -> Constr () (mkId ",") [v, v])
  , (mkId "copyShape@String", Ext () $ Primitive $ \v -> Constr () (mkId ",") [v, v])
  , (mkId "pure",       Ext () $ Primitive $ \v -> Pure () (Val nullSpan () False v))
  , (mkId "fromPure",   Ext () $ Primitive $ \(Pure () (Val nullSpan () False v)) ->  v)
  , (mkId "tick",       Pure () (Val nullSpan () False (Constr () (mkId "()") [])))
  , (mkId "intToFloat", Ext () $ Primitive $ \(NumInt n) -> NumFloat (cast n))
  , (mkId "showInt",    Ext () $ Primitive $ \n -> case n of
                              NumInt n -> StringLiteral . pack . show $ n
                              n        -> error $ show n)
  , (mkId "fromStdin", diamondConstr $ do
      when testing (error "trying to read stdin while testing")
      putStr "> "
      hFlush stdout
      val <- Text.getLine
      return $ Val nullSpan () False (StringLiteral val))

  , (mkId "readInt", diamondConstr $ do
        when testing (error "trying to read stdin while testing")
        putStr "> "
        hFlush stdout
        val <- Text.getLine
        return $ Val nullSpan () False (NumInt $ read $ unpack val))
  , (mkId "throw", diamondConstr (throwIO $ mkIOError OtherError "exc" Nothing Nothing))
  , (mkId "toStdout", Ext () $ Primitive $ \(StringLiteral s) ->
                                diamondConstr (do
                                  when testing (error "trying to write `toStdout` while testing")
                                  Text.putStr s
                                  return $ (Val nullSpan () False (Constr () (mkId "()") []))))
  , (mkId "toStderr", Ext () $ Primitive $ \(StringLiteral s) ->
                                diamondConstr (do
                                  when testing (error "trying to write `toStderr` while testing")
                                  let red x = "\ESC[31;1m" <> x <> "\ESC[0m"
                                  Text.hPutStr stderr $ red s
                                  return $ Val nullSpan () False (Constr () (mkId "()") [])))
  , (mkId "openHandle", Ext () $ Primitive openHandle)
  , (mkId "readChar", Ext () $ Primitive readChar)
  , (mkId "writeChar", Ext () $ Primitive writeChar)
  , (mkId "closeHandle",   Ext () $ Primitive closeHandle)
  , (mkId "showChar",
        Ext () $ Primitive $ \(CharLiteral c) -> StringLiteral $ pack [c])
  , (mkId "charToInt",
        Ext () $ Primitive $ \(CharLiteral c) -> NumInt $ fromEnum c)
  , (mkId "charFromInt",
        Ext () $ Primitive $ \(NumInt c) -> CharLiteral $ toEnum c)
  , (mkId "stringAppend",
        Ext () $ Primitive $ \(StringLiteral s) ->
          Ext () $ Primitive $ \(StringLiteral t) -> StringLiteral $ s <> t)
  , ( mkId "stringUncons"
    , Ext () $ Primitive $ \(StringLiteral s) -> case uncons s of
        Just (c, s) -> Constr () (mkId "Some") [Constr () (mkId ",") [CharLiteral c, StringLiteral s]]
        Nothing     -> Constr () (mkId "None") []
    )
  , ( mkId "stringCons"
    , Ext () $ Primitive $ \(CharLiteral c) ->
        Ext () $ Primitive $ \(StringLiteral s) -> StringLiteral (cons c s)
    )
  , ( mkId "stringUnsnoc"
    , Ext () $ Primitive $ \(StringLiteral s) -> case unsnoc s of
        Just (s, c) -> Constr () (mkId "Some") [Constr () (mkId ",") [StringLiteral s, CharLiteral c]]
        Nothing     -> Constr () (mkId "None") []
    )
  , ( mkId "stringSnoc"
    , Ext () $ Primitive $ \(StringLiteral s) ->
        Ext () $ Primitive $ \(CharLiteral c) -> StringLiteral (snoc s c)
    )
  , (mkId "isEOF", Ext () $ Primitive $ \(Ext _ (Handle h)) -> Ext () $ PureWrapper $ do
        b <- SIO.isEOF
        let boolflag =
             if b then Constr () (mkId "True") [] else Constr () (mkId "False") []
        return . Val nullSpan () False $ Constr () (mkId ",") [Ext () $ Handle h, boolflag])
  , (mkId "forkLinear", Ext () $ PrimitiveClosure forkLinear)
  , (mkId "forkLinear'", Ext () $ PrimitiveClosure forkLinear')
  , (mkId "fork",    Ext () $ PrimitiveClosure forkRep)
  , (mkId "recv",    Ext () $ Primitive recv)
  , (mkId "send",    Ext () $ Primitive send)
  , (mkId "close",   Ext () $ Primitive close)
  , (mkId "grecv",    Ext () $ Primitive grecv)
  , (mkId "gsend",    Ext () $ Primitive gsend)
  , (mkId "gclose",   Ext () $ Primitive gclose)
  -- , (mkId "trace",   Ext () $ Primitive $ \(StringLiteral s) -> diamondConstr $ do { Text.putStr s; hFlush stdout; return $ Val nullSpan () False (Constr () (mkId "()") []) })
  -- , (mkId "newPtr", malloc)
  -- , (mkId "swapPtr", peek poke castPtr) -- hmm probably don't need to cast the Ptr
  -- , (mkId "freePtr", free)
  , (mkId "uniqueReturn",  Ext () $ Primitive uniqueReturn)
  , (mkId "uniqueBind",    Ext () $ PrimitiveClosure uniqueBind)
  , (mkId "uniquePush",    Ext () $ Primitive uniquePush)
  , (mkId "uniquePull",    Ext () $ Primitive uniquePull)
  , (mkId "newFloatArray",  Ext () $ Primitive newFloatArray)
  , (mkId "lengthFloatArray",  Ext () $ Primitive lengthFloatArray)
  , (mkId "readFloatArray",  Ext () $ Primitive readFloatArray)
  , (mkId "writeFloatArray",  Ext () $ Primitive writeFloatArray)
  , (mkId "newFloatArray'",  Ext () $ Primitive newFloatArray')
  , (mkId "lengthFloatArray'",  Ext () $ Primitive lengthFloatArray')
  , (mkId "readFloatArray'",  Ext () $ Primitive readFloatArray')
  , (mkId "writeFloatArray'",  Ext () $ Primitive writeFloatArray')

  ]
  where
    forkLinear :: (?globals :: Globals) => Ctxt RValue -> RValue -> RValue
    forkLinear ctxt e@Abs{} = Ext () (unsafePerformIO $ do
      c <- CC.newChan
      _ <- C.forkIO $
         evalIn ctxt (App nullSpan () False (valExpr e) (valExpr $ Ext () $ Chan c)) >> return ()
      return $ Chan c)
    forkLinear ctxt e = error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    forkLinear' :: (?globals :: Globals) => Ctxt RValue -> RValue -> RValue
    forkLinear' ctxt e@Abs{} = Ext () (unsafePerformIO $ do
      c <- CC.newChan
      _ <- C.forkIO $
         evalIn ctxt (App nullSpan () False
                        (valExpr e)
                        (valExpr $ Promote () $ valExpr $ Ext () $ Chan c)) >> return ()
      return $ Chan c)
    forkLinear' ctxt e = error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    forkRep :: (?globals :: Globals) => Ctxt RValue -> RValue -> RValue
    forkRep ctxt e@Abs{} = diamondConstr $ do
      c <- CC.newChan
      _ <- C.forkIO $
         evalIn ctxt (App nullSpan () False
                        (valExpr e)
                        (valExpr $ Promote () $ valExpr $ Ext () $ Chan c)) >> return ()
      return $ valExpr $ Promote () $ valExpr $ Ext () $ Chan c
    forkRep ctxt e = error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    uniqueReturn :: RValue -> RValue
    uniqueReturn (Nec () v) = (Promote () v)
    uniqueReturn v = error $ "Bug in Granule. Can't borrow a non-unique: " <> prettyDebug v

    uniqueBind :: (?globals :: Globals) => Ctxt RValue -> RValue -> RValue
    uniqueBind ctxt f = Ext () $ Primitive $ \(Promote () v) -> 
      unsafePerformIO $ evalIn ctxt 
        (App nullSpan () False 
          (Val nullSpan () False f) 
          (Val nullSpan () False (Nec () v)))

    uniquePush :: RValue -> RValue
    uniquePush (Nec () (Val nullSpan () False (Constr () (Id "," ",") [x, y])))
     = (Constr () (mkId ",") [(Nec () (Val nullSpan () False x)), (Nec () (Val nullSpan () False y))])
    uniquePush v = error $ "Bug in Granule. Can't push through a non-unique: " <> prettyDebug v

    uniquePull :: RValue -> RValue
    uniquePull (Constr () (Id "," ",") [(Nec () (Val nullSpan () False x)), (Nec () (Val _ () False y))])
      = (Nec () (Val nullSpan () False (Constr () (mkId ",") [x, y])))
    uniquePull v = error $ "Bug in Granule. Can't pull through a non-unique: " <> prettyDebug v

    recv :: (?globals :: Globals) => RValue -> RValue
    recv (Ext _ (Chan c)) = unsafePerformIO $ do
      x <- CC.readChan c
      return $ Constr () (mkId ",") [x, Ext () $ Chan c]
    recv e = error $ "Bug in Granule. Trying to recevie from: " <> prettyDebug e

    send :: (?globals :: Globals) => RValue -> RValue
    send (Ext _ (Chan c)) = Ext () $ Primitive
      (\v -> unsafePerformIO $ do
         CC.writeChan c v
         return $ Ext () $ Chan c)
    send e = error $ "Bug in Granule. Trying to send from: " <> prettyDebug e

    close :: RValue -> RValue
    close (Ext _ (Chan c)) = unsafePerformIO $ return $ Constr () (mkId "()") []
    close rval = error $ "Runtime exception: trying to close a value which is not a channel"

    grecv :: (?globals :: Globals) => RValue -> RValue
    grecv (Ext _ (Chan c)) = diamondConstr $ do
      x <- CC.readChan c
      return $ valExpr $ Constr () (mkId ",") [x, Ext () $ Chan c]
    grecv e = error $ "Bug in Granule. Trying to recevie from: " <> prettyDebug e

    gsend :: (?globals :: Globals) => RValue -> RValue
    gsend (Ext _ (Chan c)) = Ext () $ Primitive
      (\v -> diamondConstr $ do
         CC.writeChan c v
         return $ valExpr $ Ext () $ Chan c)
    gsend e = error $ "Bug in Granule. Trying to send from: " <> prettyDebug e

    gclose :: RValue -> RValue
    gclose (Ext _ (Chan c)) = diamondConstr $ return $ valExpr $ Constr () (mkId "()") []
    gclose rval = error $ "Runtime exception: trying to close a value which is not a channel"

    cast :: Int -> Double
    cast = fromInteger . toInteger

    openHandle :: RValue -> RValue
    openHandle (Constr _ m []) =
      Ext () $ Primitive (\x -> diamondConstr (
        case x of
          (StringLiteral s) -> do
            h <- SIO.openFile (unpack s) mode
            return $ valExpr $ Ext () $ Handle h
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
      Ext () $ Primitive (\c -> diamondConstr (
        case c of
          (CharLiteral c) -> do
            SIO.hPutChar h c
            return $ valExpr $ Ext () $ Handle h
          _ -> error $ "Runtime exception: trying to put a non character value"))
    writeChar _ = error $ "Runtime exception: trying to put from a non handle value"

    readChar :: RValue -> RValue
    readChar (Ext _ (Handle h)) = diamondConstr $ do
          c <- SIO.hGetChar h
          return $ valExpr (Constr () (mkId ",") [Ext () $ Handle h, CharLiteral c])
    readChar h = error $ "Runtime exception: trying to get from a non handle value" <> prettyDebug h

    closeHandle :: RValue -> RValue
    closeHandle (Ext _ (Handle h)) = diamondConstr $ do
         SIO.hClose h
         return $ valExpr (Constr () (mkId "()") [])
    closeHandle _ = error $ "Runtime exception: trying to close a non handle value"

    {-# NOINLINE newFloatArray #-}
    newFloatArray :: RValue -> RValue
    newFloatArray = \(NumInt i) -> Nec () (Val nullSpan () False $ Ext () $ FloatArray (unsafePerformIO (MA.newArray_ (0,i))))

    {-# NOINLINE newFloatArray' #-}
    newFloatArray' :: RValue -> RValue
    newFloatArray' = \(NumInt i) -> Promote () (Val nullSpan () False $ Ext () $ FloatArray (unsafePerformIO (MA.newArray_ (0,i))))

    {-# NOINLINE readFloatArray #-}
    readFloatArray :: RValue -> RValue
    readFloatArray = \(Nec () (Val _ _ _ (Ext () (FloatArray arr)))) -> Ext () $ Primitive $ \(NumInt i) ->
      unsafePerformIO $ do e <- MA.readArray arr i
                           return (Constr () (mkId ",") [NumFloat e, Nec () (Val nullSpan () False $ Ext () (FloatArray arr))])

    {-# NOINLINE readFloatArray' #-}
    readFloatArray' :: RValue -> RValue
    readFloatArray' = \(Promote () (Val _ _ _ (Ext () (FloatArray arr)))) -> Ext () $ Primitive $ \(NumInt i) ->
      unsafePerformIO $ do e <- MA.readArray arr i
                           return (Constr () (mkId ",") [NumFloat e, Promote () (Val nullSpan () False $ Ext () (FloatArray arr))])

    lengthFloatArray :: RValue -> RValue
    lengthFloatArray = \(Nec () (Val _ _ _ (Ext () (FloatArray arr)))) -> Ext () $ Primitive $ \(NumInt i) ->
      unsafePerformIO $ do (_,end) <- MA.getBounds arr
                           return (Constr () (mkId ",") [NumInt end, Nec () (Val nullSpan () False $ Ext () $ FloatArray arr)])

    lengthFloatArray' :: RValue -> RValue
    lengthFloatArray' = \(Promote () (Val _ _ _ (Ext () (FloatArray arr)))) -> Ext () $ Primitive $ \(NumInt i) ->
      unsafePerformIO $ do (_,end) <- MA.getBounds arr
                           return (Constr () (mkId ",") [NumInt end, Promote () (Val nullSpan () False $ Ext () $ FloatArray arr)])

    {-# NOINLINE writeFloatArray #-}
    writeFloatArray :: RValue -> RValue
    writeFloatArray = \(Nec _ (Val _ _ _ (Ext _ (FloatArray arr)))) ->
      Ext () $ Primitive $ \(NumInt i) ->
      Ext () $ Primitive $ \(NumFloat v) ->
      Nec () $ Val nullSpan () False $ Ext () $ FloatArray $ unsafePerformIO $
        do () <- MA.writeArray arr i v
           return arr

    {-# NOINLINE writeFloatArray' #-}
    writeFloatArray' :: RValue -> RValue
    writeFloatArray' = \(Promote _ (Val _ _ _ (Ext _ (FloatArray arr)))) ->
      Ext () $ Primitive $ \(NumInt i) ->
      Ext () $ Primitive $ \(NumFloat v) ->
      Promote () $ Val nullSpan () False $ Ext () $ FloatArray $ unsafePerformIO $
        do arr' <- MA.mapArray id arr
           () <- MA.writeArray arr' i v
           return arr'

evalDefs :: (?globals :: Globals) => Ctxt RValue -> [Def (Runtime ()) ()] -> IO (Ctxt RValue)
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
  toRuntimeRep :: t () () -> t (Runtime ()) ()

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
  toRuntimeRep (Case s a rf e ps) = Case s a rf (toRuntimeRep e) (map (second toRuntimeRep) ps)
  toRuntimeRep (Hole s a rf vs) = Hole s a rf vs

instance RuntimeRep Value where
  toRuntimeRep (Ext a ()) = error "Bug: Parser generated an extended value case when it shouldn't have"
  toRuntimeRep (Abs a p t e) = Abs a p t (toRuntimeRep e)
  toRuntimeRep (Promote a e) = Promote a (toRuntimeRep e)
  toRuntimeRep (Pure a e) = Pure a (toRuntimeRep e)
  toRuntimeRep (Nec a e) = Nec a (toRuntimeRep e)
  toRuntimeRep (Constr a i vs) = Constr a i (map toRuntimeRep vs)
  -- identity cases
  toRuntimeRep (CharLiteral c) = CharLiteral c
  toRuntimeRep (StringLiteral c) = StringLiteral c
  toRuntimeRep (Var a x) = Var a x
  toRuntimeRep (NumInt x) = NumInt x
  toRuntimeRep (NumFloat x) = NumFloat x

eval :: (?globals :: Globals) => AST () () -> IO (Maybe RValue)
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
      Just (Nec _ e) -> fmap Just (evalIn bindings e)
      -- ... or a regular value came out of the interpreter
      Just val           -> return $ Just val
