-- Granule interpreter
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}


{-# options_ghc -Wno-incomplete-uni-patterns #-}

module Language.Granule.Interpreter.Eval where

import Language.Granule.Interpreter.Desugar
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span (nullSpanNoFile)
import Language.Granule.Context
import Language.Granule.Utils (nullSpan, Globals, globalsExtensions, entryPoint, Extension(..))
import Language.Granule.Runtime as RT

import Data.Text (cons, uncons, unpack, snoc, unsnoc)
import Control.Monad (foldM)

import System.IO.Unsafe (unsafePerformIO)
--import Control.Exception (catch, throwIO, IOException)
import Control.Exception (catch, IOException)
--import GHC.IO.Exception (IOErrorType( OtherError ))
import qualified Control.Concurrent as C (forkIO)
import qualified Control.Concurrent.Chan as CC (newChan, writeChan, readChan, dupChan, Chan)
import qualified Control.Concurrent.MVar as MV
import qualified System.IO as SIO

--import System.IO.Error (mkIOError)
import Data.Bifunctor
import Control.Monad.Extra (void)

type RValue = Value (Runtime ()) ()
type RExpr = Expr (Runtime ()) ()
type PrimFun a = Value (Runtime a) a -> IO (Value (Runtime a) a)

-- | Runtime values only used in the interpreter
data Runtime a =
  -- | Primitive functions (builtins)
    Primitive (PrimFun a)

  -- | Primitive operations that also close over the context
  | PrimitiveClosure (Ctxt (Value (Runtime a) a) -> PrimFun a)

  -- | File handler
  | Handle SIO.Handle

  -- | Channels
  | Chan (BinaryChannel a)

  -- | Delayed side effects wrapper
  | PureWrapper (IO (Expr (Runtime a) ()))

  -- | Data managed by the runtime module (mutable arrays)
  | Runtime RuntimeData

-- Dual-ended channel
data BinaryChannel a =
       BChan { fwd :: CC.Chan (Value (Runtime a) a)
             , bwd :: CC.Chan (Value (Runtime a) a)
             , putbackFwd :: MV.MVar (Value (Runtime a) a)
             , putbackBwd :: MV.MVar (Value (Runtime a) a)
             , tag :: Prelude.String -- if this is not "" then debugging messages get output
             , pol :: Bool } -- polarity

-- Channel primitive wrapps
dualEndpoint :: BinaryChannel a -> BinaryChannel a
dualEndpoint (BChan fwd bwd mFwd mBwd t pol) = BChan bwd fwd mBwd mFwd t (not pol)

debugComms :: Prelude.String -> Bool -> Prelude.String -> IO ()
debugComms "" _ x = return ()
debugComms tag True x = putStrLn $ "[" ++ tag ++ " ->]: " ++ x
debugComms tag False x = putStrLn $ "[" ++ tag ++ " <-]: " ++ x

newChan :: IO (BinaryChannel a)
newChan = do
  c  <- CC.newChan
  c' <- CC.newChan
  m  <- MV.newEmptyMVar
  m'  <- MV.newEmptyMVar
  return $ BChan c c' m m' "" True

-- Adds a tag (channel name) for debugging
newChan' :: Prelude.String -> IO (BinaryChannel a)
newChan' tag = do
  c  <- CC.newChan
  c' <- CC.newChan
  m  <- MV.newEmptyMVar
  m'  <- MV.newEmptyMVar
  return $ BChan c c' m m' tag True

readChan :: BinaryChannel () -> IO RValue
readChan (BChan _ bwd _ bwdMV tag pol) = do
  flag <- MV.isEmptyMVar bwdMV
  if flag
    then do
      debugComms tag pol $ "Read Normal"
      x <- CC.readChan bwd
      debugComms tag pol $ "READ " ++ show x
      return x
    -- short-circuit the channel because a value was read and has been memo
    else do
      debugComms tag pol $ "Read Putback"
      x <- MV.takeMVar bwdMV
      debugComms tag pol $ "READ from put back: " ++ show x
      return x

putbackChan :: BinaryChannel a -> (Value (Runtime a) a) -> IO ()
putbackChan (BChan _ _ _ bwdMV tag pol) x = do
  debugComms tag pol "Putback"
  MV.putMVar bwdMV x

writeChan :: Show a => BinaryChannel a -> (Value (Runtime a) a) -> IO ()
writeChan (BChan fwd _ _ _ tag pol) v = do
  debugComms tag pol $ "Try to write " ++ show v
  CC.writeChan fwd v
  debugComms tag pol $ "written"

dupChan :: BinaryChannel a -> IO (BinaryChannel a)
dupChan (BChan fwd bwd m n t p) = do
  fwd' <- CC.dupChan fwd
  bwd' <- CC.dupChan bwd
  -- Behaviour here with the putback mvar is a bit weak, should not used in this way with dupChan
  return $ BChan fwd' bwd' m n (t ++ t) p

---

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
  show (Runtime _) = "<array>"

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
      (CharLiteral n1, CharLiteral n2) -> Constr () (mkId . show $ n1 == n2) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ n1 == n2) []
      -- This seems very bad
      (v1, v2) -> Constr () (mkId $ show (show v1 == show v2)) []
      -- _ -> evalFail
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

-- Evaluate an expression to normal form, but use CBN reduction throughout
evalInCBNdeep :: (?globals :: Globals) => Ctxt RValue -> RExpr -> IO RValue
evalInCBNdeep ctxt (App s a b e1 e2) = do
    -- (cf. APP_L)
    v1 <- evalInCBNdeep ctxt e1
    case v1 of
      (Ext _ (Primitive k)) -> do
        -- (cf. APP_R)
        -- Force eval of the parameter for primitives
        v2 <- evalInCBNdeep ctxt e2
        vRes <- k v2
        return vRes

      (Abs _ p _ e3) -> do
        -- (cf. P_BETA CBN)
        pResult <- pmatchCBN ctxt [(p, e3)] e2
        case pResult of
          Just e3' -> evalInCBNdeep ctxt e3'
          _ -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " against " <> pretty e2 <> " in application at " <> pretty s

      (Constr s' c vs) -> do
        v2 <- evalInCBNdeep ctxt e2
        return $ Constr s' c (vs ++ [v2])

      _ -> error $ "CBNdeep: LHS of an application is not a function value " ++ pretty v1
      -- _ -> error "Cannot apply value"

evalInCBNdeep ctxt (Val s a b (Var _ x)) =
    case lookup x ctxt of
      Just val@(Ext _ (PrimitiveClosure f)) -> return $ Ext () $ Primitive (f ctxt)
      Just val -> return val
      Nothing  -> fail $ "Variable '" <> sourceName x <> "' is undefined in context."

evalInCBNdeep ctxt (Val _ _ _ v) = return v

evalInCBNdeep ctxt e = do
  e' <- evalInWHNF ctxt e
  evalInCBNdeep ctxt e'

-- Evaluate an expression to weak head normal form.
evalInWHNF :: (?globals :: Globals) => Ctxt RValue -> RExpr -> IO RExpr
evalInWHNF ctxt (App s a b e1 e2) = do
    -- (cf. APP_L)
    v1 <- evalInWHNF ctxt e1
    case v1 of
      (Val _ _ _ (Ext _ (Primitive k))) -> do
        -- (cf. APP_R)
        -- Force eval of the parameter for primitives
        v2 <- evalIn ctxt e2
        vRes <- k v2
        return $ Val s a b vRes

      (Val _ _ _ (Abs _ p _ e3)) -> do
        -- (cf. P_BETA CBN)
        pResult <- pmatchCBN ctxt [(p, e3)] e2
        case pResult of
          Just e3' -> return e3'
          _ -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in application at " <> pretty s

      (Val _ _ _ (Constr _ c vs)) -> do
        return $ App s a b v1 e2

      _ -> error $ "LHS of an application is not a function value " ++ pretty v1
      -- _ -> error "Cannot apply value"

-- Deriving applications get resolved to their names
evalInWHNF ctxt (AppTy _ _ _ (Val s a rf (Var a' n)) t) | internalName n `elem` ["push", "pull", "copyShape", "drop"] =
  evalInWHNF ctxt (Val s a rf (Var a' (mkId $ pretty n <> "@" <> pretty t)))

-- Other type applications have no run time component (currently)
evalInWHNF ctxt (AppTy s _ _ e t) =
  evalInWHNF ctxt e

evalInWHNF ctxt (Binop s a b op e1 e2) = do
     v1 <- evalIn ctxt e1
     v2 <- evalIn ctxt e2
     return $ Val s a b $ evalBinOp op v1 v2
     --   (v1', v2') -> error $ "CBN reduction failed on (" ++ pretty v1 ++ " " ++ pretty op ++ " " ++ pretty v2 ++ ")"

evalInWHNF ctxt (LetDiamond s _ _ p _ e1 e2) = do
  -- (cf. LET_1)
  v1 <- evalInWHNF ctxt e1
  case v1 of
    (Val _ _ _ (isDiaConstr -> Just e)) -> do
        -- Do the delayed side effect
        eInner <- e
        -- (cf. LET_2)
        v1' <- evalInWHNF ctxt eInner
        -- (cf. LET_BETA)
        pResult  <- pmatch ctxt [(p, e2)] v1'
        case pResult of
          Just e2' ->
              evalInWHNF ctxt e2'
          Nothing -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in let at " <> pretty s

    other -> fail $ "Runtime exception: Expecting a diamonad value but got: "
                      <> prettyDebug other

evalInWHNF ctxt (Val s a b (Var _ x)) =
    case lookup x ctxt of
      Just val@(Ext _ (PrimitiveClosure f)) -> return $ Val s a b $ Ext () $ Primitive (f ctxt)
      Just val -> return $ Val s a b $ val
      Nothing  -> fail $ "Variable '" <> sourceName x <> "' is undefined in context."

evalInWHNF _ e@(Val _ _ _ v) = return e

evalInWHNF ctxt e@(Case s a b guardExpr cases) = do
  p <- pmatchCBN ctxt cases guardExpr
  case p of
    Just ei -> return ei
    Nothing ->
          error $ "Incomplete pattern match:\n  cases: "
              <> pretty cases <> "\n  expr: " <> pretty guardExpr

evalInWHNF ctxt (Unpack s a rf tyVar var e1 e2) = do
  e1' <- evalInWHNF ctxt e1
  case e1' of
    (Val _ _ _ (Pack _ _ ty eInner _ _ _)) -> do
      p <- pmatch ctxt [(PVar s () False var, e2)] eInner
      case p of
        Just ei -> return ei
        Nothing -> error $ "Failed pattern match for unpack on " <> pretty e1'
    other ->
      evalInWHNF ctxt (Unpack s a rf tyVar var e1' e2)


evalInWHNF ctxt Hole {} =
  error "Trying to evaluate a hole, which should not have passed the type checker."

evalInWHNF ctxt TryCatch {} =
  error "TryCatch is not supported by the CBN extension yet."


-- Call-by-value big step semantics
evalIn :: (?globals :: Globals) => Ctxt RValue -> RExpr -> IO RValue
evalIn ctxt e =
  if CBN `elem` globalsExtensions ?globals
    then do
      e' <- evalInCBNdeep ctxt e
      -- finally eagerly evaluate
      e'' <- evalInCBV ctxt (valExpr e')
      return e''

    else evalInCBV ctxt e


evalInCBV :: (?globals :: Globals) => Ctxt RValue -> RExpr -> IO RValue
evalInCBV ctxt (App s _ _ e1 e2) = do
    -- (cf. APP_L)
    v1 <- evalInCBV ctxt e1
    case v1 of
      (Ext _ (Primitive k)) -> do
        -- (cf. APP_R)
        v2 <- evalInCBV ctxt e2
        k v2

      Abs _ p _ e3 -> do
        -- (cf. APP_R)
        v2 <- evalInCBV ctxt e2
        -- (cf. P_BETA)
        pResult <- pmatch ctxt [(p, e3)] (valExpr v2)
        case pResult of
          Just e3' -> evalInCBV ctxt e3'
          _ -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " against " <> pretty v2 <> " in application at " <> pretty s

      Constr _ c vs -> do
        -- (cf. APP_R)
        v2 <- evalInCBV ctxt e2
        return $ Constr () c (vs <> [v2])

      _ -> error $ show v1
      -- _ -> error "Cannot apply value"

-- Deriving applications get resolved to their names
evalInCBV ctxt (AppTy _ _ _ (Val s a rf (Var a' n)) t) | internalName n `elem` ["push", "pull", "copyShape", "drop"] =
  evalInCBV ctxt (Val s a rf (Var a' (mkId $ pretty n <> "@" <> pretty t)))

-- Other type applications have no run time component (currently)
evalInCBV ctxt (AppTy s _ _ e t) =
  evalInCBV ctxt e

evalInCBV ctxt (Binop _ _ _ op e1 e2) = do
     v1 <- evalInCBV ctxt e1
     v2 <- evalInCBV ctxt e2
     return $ evalBinOp op v1 v2

evalInCBV ctxt (LetDiamond s _ _ p _ e1 e2) = do
  -- (cf. LET_1)
  v1 <- evalInCBV ctxt e1
  case v1 of
    (isDiaConstr -> Just e) -> do
        -- Do the delayed side effect
        eInner <- e
        -- (cf. LET_2)
        v1' <- evalInCBV ctxt eInner
        -- (cf. LET_BETA)
        pResult  <- pmatch ctxt [(p, e2)] (valExpr v1')
        case pResult of
          Just e2' ->
              evalInCBV ctxt e2'
          Nothing -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in let at " <> pretty s

    other -> fail $ "Runtime exception: Expecting a diamonad value but got: "
                      <> prettyDebug other

evalInCBV ctxt (TryCatch s _ _ e1 p _ e2 e3) = do
  v1 <- evalInCBV ctxt e1
  case v1 of
    (isDiaConstr -> Just e) ->
      catch ( do
        eInner <- e
        e1' <- evalInCBV ctxt eInner
        pmatch ctxt [(PBox s () False p, e2)] (valExpr e1') >>=
          \case
            Just e2' -> evalInCBV ctxt e2'
            Nothing -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in try at " <> pretty s
      )
       -- (cf. TRY_BETA_2)
      (\(e :: IOException) -> evalInCBV ctxt e3)
    other -> fail $ "Runtime exception: Expecting a diamond value but got: " <> prettyDebug other

evalInCBV ctxt (Unpack s a rf tyVar var e1 e2) = do
  v1 <- evalInCBV ctxt e1
  case v1 of
    (Pack _ _ ty eInner _ _ _) -> do
      v <- evalInCBV ctxt eInner
      pmatch ctxt [(PVar s () False var, e2)] (valExpr v) >>=
        \case
          Just e2' -> evalInCBV ctxt e2'
          Nothing  -> fail $ "Runtime exception: Failed pattern match " <> pretty var <> " in try at " <> pretty s
    other -> fail $ "Runtime exception: Expecting a pack value but got: " <> prettyDebug other

{-
-- Hard-coded 'scale', removed for now
evalInCBV _ (Val _ _ _ (Var _ v)) | internalName v == "scale" = return
  (Abs () (PVar nullSpan () False $ mkId " x") Nothing (Val nullSpan () False
    (Abs () (PVar nullSpan () False $ mkId " y") Nothing (
      letBox nullSpan (PVar nullSpan () False $ mkId " ye")
         (Val nullSpan () False (Var () (mkId " y")))
         (Binop nullSpan () False
           OpTimes (Val nullSpan () False (Var () (mkId " x"))) (Val nullSpan () False (Var () (mkId " ye"))))))))
-}

evalInCBV ctxt (Val _ _ _ (Var _ x)) =
    case lookup x ctxt of
      Just val@(Ext _ (PrimitiveClosure f)) -> return $ Ext () $ Primitive (f ctxt)
      Just val -> return val
      Nothing  -> fail $ "Variable '" <> sourceName x <> "' is undefined in context. Context is " <> show ctxt

evalInCBV ctxt (Val s _ _ (Promote _ e)) =
  if CBN `elem` globalsExtensions ?globals
    then do
      return $ Promote () e
    else do
      -- (cf. Box)
      v <- evalInCBV ctxt e
      return $ Promote () (Val s () False v)

evalInCBV ctxt (Val s _ _ (Nec _ e)) =
  if CBN `elem` globalsExtensions ?globals
    then do
      return $ Nec () e
    else do
      v <- evalInCBV ctxt e
      return $ Nec () (Val s () False v)

evalInCBV _ (Val _ _ _ v) = return v

evalInCBV ctxt (Case s a b guardExpr cases) = do
  v <- evalInCBV ctxt guardExpr
  p <- pmatch ctxt cases (Val s a b v)
  case p of
    Just ei -> evalInCBV ctxt ei
    Nothing             ->
      error $ "Incomplete pattern match:\n  cases: "
          <> pretty cases <> "\n  expr: " <> pretty v

evalInCBV ctxt Hole {} =
  error "Trying to evaluate a hole, which should not have passed the type checker."

applyBindings :: Ctxt RExpr -> RExpr -> RExpr
applyBindings [] e = e
applyBindings ((var, e'):bs) e = applyBindings bs (subst e' var e)

-- matchOrTriggerReduction :: Ctxt RValue -> (Expr a -> Maybe (IO b)) -> Expr a -> IO (Maybe b)
-- matchOrTriggerReduction ctxt matcher e =
--   case matcher e of
--     Just k  -> k >>= (return . Just)
--     Nothing -> do
--       e' <- evalIn ctxt e
--       case matcher e' of
--         Just k  -> k >>= (return . Just)
--         Nothing -> return Nothing


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
pmatch = if CBN `elem` globalsExtensions ?globals then pmatchCBN else pmatchCBV

-- CBN version of pattern matching
pmatchCBN :: (?globals :: Globals)
  => Ctxt RValue
  -> [(Pattern (), RExpr)]
  -> RExpr
  -> IO (Maybe RExpr)
pmatchCBN _ [] _ =
  return Nothing

pmatchCBN _ ((PWild {}, eb):_) _ =
  return $ Just eb

pmatchCBN _ ((PVar _ _ _ var, eb):_) eg =
  return $ Just $ subst eg var eb

pmatchCBN ctxt psAll@((PBox _ _ _ p, eb):ps) eg =
  case eg of
    -- Match
    (Val _ _ _ (Promote _ eg')) -> do
      match <- pmatchCBN ctxt [(p, eb)] eg'
      case match of
        Just e  -> return $ Just e
        -- Try rest
        Nothing -> pmatchCBN ctxt ps eg

    _ -> do
      if isReducible eg
        -- Trigger reduction
        then do
          eg' <- evalInWHNF ctxt eg
          pmatchCBN ctxt psAll eg'
        -- No match
        else
          pmatchCBN ctxt ps eg

pmatchCBN ctxt psAll@(p@(PConstr _ _ _ id innerPs, eb):ps) eg = do
  case constructorApplicationSpine eg of

    -- Trigger reduction
    Nothing -> do
      eg' <- evalInWHNF ctxt eg
      -- ... and re-enter pattern match
      pmatchCBN ctxt psAll eg'

    -- Possible match
    Just (id', valArgs) -> do
      if id == id' && length innerPs == length valArgs
        -- Match
        then do
          -- Fold over the inner patterns trying to match (and reducing along the way)
          ebFinal <- foldM (\ebM (pi, vi) -> case ebM of
                                      Nothing -> return Nothing
                                      Just eb -> pmatchCBN ctxt [(pi, eb)] vi) (Just eb) (zip innerPs valArgs)
          case ebFinal of
            -- Success!
            Just ebFinal' -> return $ Just ebFinal'
            -- There was a failure somewhere so skip this pattern
            Nothing  -> pmatchCBN ctxt ps eg

        -- No match
        else pmatchCBN ctxt ps eg

pmatchCBN ctxt psAll@((PInt _ _ _ n, eb):ps) eg =
  case eg of
    -- Match
    (Val _ _ _ (NumInt m)) | n == m -> return $ Just eb
    _ ->
        if isReducible eg
        -- Trigger reduction
        then do
          eg' <- evalInWHNF ctxt eg
          pmatchCBN ctxt psAll eg'
        -- No match
        else
          pmatchCBN ctxt ps eg

pmatchCBN ctxt psAll@((PFloat _ _ _ n, eb):ps) eg =
  case eg of
    -- Match
    (Val _ _ _ (NumFloat m)) | n == m -> return $ Just eb
    _ ->
        if isReducible eg
        -- Trigger reduction
        then do
          eg' <- evalInWHNF ctxt eg
          pmatchCBN ctxt psAll eg'
        -- No match
        else
          pmatchCBN ctxt ps eg

-- CBV version of pattern matching
pmatchCBV ::
  (?globals :: Globals)
  => Ctxt RValue
  -> [(Pattern (), RExpr)]
  -> RExpr
  -> IO (Maybe RExpr)

pmatchCBV _ [] _ =
  return Nothing

pmatchCBV _ ((PWild {}, e):_)  _ =
  return $ Just e

pmatchCBV ctxt ((PConstr _ _ _ id innerPs, t0):ps) v@(Val s a b (Constr _ id' vs))
 | id == id' && length innerPs == length vs = do

  -- Fold over the inner patterns
  let vs' = map valExpr vs
  tLastM <- foldM (\tiM (pi, vi) -> case tiM of
                                      Nothing -> return Nothing
                                      Just ti -> pmatchCBV ctxt [(pi, ti)] vi) (Just t0) (zip innerPs vs')

  case tLastM of
    Just tLast -> return $ Just tLast
    -- There was a failure somewhere
    Nothing  -> pmatchCBV ctxt ps v

pmatchCBV _ ((PVar _ _ _ var, e):_) v =
  return $ Just $ subst v var e

pmatchCBV ctxt ((PBox _ _ _ p, e):ps) v@(Val _ _ _ (Promote _ v')) = do
  match <- pmatchCBV ctxt [(p, e)] v'
  case match of
    Just e -> return $ Just e
    Nothing -> pmatchCBV ctxt ps v

pmatchCBV ctxt ((PInt _ _ _ n, e):ps) (Val _ _ _ (NumInt m)) =
  if n == m
    then return $ Just e
    else pmatchCBV ctxt ps e

pmatchCBV ctxt ((PFloat _ _ _ n, e):ps) (Val _ _ _ (NumFloat m)) =
  if n == m
    then return $ Just e
    else pmatchCBV ctxt ps e

pmatchCBV ctxt (_:ps) v = pmatchCBV ctxt ps v

-- Wrap a value into an expression
valExpr :: ExprFix2 g ExprF ev () -> ExprFix2 ExprF g ev ()
valExpr = Val nullSpanNoFile () False

builtIns :: (?globals :: Globals) => Ctxt RValue
{-# NOINLINE builtIns #-}
builtIns =
  [
    (mkId "div", Ext () $ Primitive $ \(NumInt n1)
          -> return $ Ext () $ Primitive $ \(NumInt n2) -> return $ NumInt (n1 `div` n2))
  , (mkId "use", Ext () $ Primitive $ \v -> return $ Promote () (Val nullSpan () False v))
  , (mkId "compose", Ext () $ Primitive $ \g -> return $
                                Ext () $ Primitive $ \f -> return $
                                  Abs () (PVar nullSpan () False (mkId "xc")) Nothing
                                    (App nullSpan () False (Val nullSpan () False g) (App nullSpan () False (Val nullSpan () False f)
                                        (Val nullSpan () False (Var () (mkId "xc"))))))

  -- differental privacy/sensitivty tracking version of scaling
  , (mkId "scale", Ext () $ Primitive $ \(NumFloat n) -> return $
      Ext () $ Primitive $ \(Promote () (Val nullSpan () _ (NumFloat m))) ->
        return $ NumFloat (n * m))
  -- capabilities
  , (mkId "cap", Ext () $ Primitive $ \(Constr () name _) -> return $ Ext () $ Primitive $ \_ ->
       case internalName name of
         "Console" -> return $ Ext () $ Primitive $ \(StringLiteral s) -> toStdout s >>
                          (return $ (Constr () (mkId "()") []))
         "TimeDate" -> return $ Ext () $ Primitive $ \(Constr () (internalName -> "()") []) -> RT.timeDate () >>=
                          (\s -> return $ (StringLiteral s))
         _ -> error "Unknown capability")
  -- substrctural combinators
  , (mkId "moveChar", Ext () $ Primitive $ \(CharLiteral c) -> return $ Promote () (Val nullSpan () False (CharLiteral c)))
  , (mkId "moveInt", Ext () $ Primitive $ \(NumInt c) -> return $ Promote () (Val nullSpan () False (NumInt c)))
  , ( mkId "moveString"
    , Ext () $ Primitive $ \(StringLiteral s) -> return $
        Promote () $ valExpr $ (StringLiteral s))
  , (mkId "drop@Int", Ext () $ Primitive $ const $ return $ Constr () (mkId "()") [])
  , (mkId "drop@Char", Ext () $ Primitive $ const $ return $ Constr () (mkId "()") [])
  , (mkId "drop@Float", Ext () $ Primitive $ const $ return $ Constr () (mkId "()") [])
  , (mkId "drop@String", Ext () $ Primitive $ const $ return $ Constr () (mkId "()") [])
  , (mkId "drop@FloatArray", Ext () $ Primitive $ const $ return $ Constr () (mkId "()") [])
  , (mkId "pure",       Ext () $ Primitive $ \v -> return $ Pure () (Val nullSpan () False v))
  , (mkId "fromPure",   Ext () $ Primitive $ \(Pure () (Val nullSpan () False v)) -> return v)
  , (mkId "tick",       Pure () (Val nullSpan () False (Constr () (mkId "()") [])))
  , (mkId "intToFloat", Ext () $ Primitive $ \(NumInt n) -> return $ NumFloat $ RT.intToFloat n)
  , (mkId "showInt",    Ext () $ Primitive $ \case
                              NumInt n -> return $ StringLiteral . RT.showInt $ n
                              n        -> error $ show n)
  , (mkId "showFloat",    Ext () $ Primitive $ \case
                              NumFloat n -> return $ StringLiteral . RT.showFloat $ n
                              n        -> error $ show n)
  , (mkId "readInt",    Ext () $ Primitive $ \(StringLiteral s) -> return $ NumInt $ RT.readInt s)
  , (mkId "fromStdin", diamondConstr $ RT.fromStdin >>= \val -> return $ Val nullSpan () False $ StringLiteral val)
  , (mkId "toStdout",  Ext () $ Primitive $ \(StringLiteral s) -> return $ diamondConstr $ (toStdout s) >>
      (return $ Val nullSpan () False (Constr () (mkId "()") [])))
  , (mkId "toStderr", Ext () $ Primitive $ \(StringLiteral s) -> return $ diamondConstr $ (toStderr s) >>
      (return $ Val nullSpan () False (Constr () (mkId "()") [])))
  , (mkId "openHandle", Ext () $ Primitive openHandle)
  , (mkId "readChar", Ext () $ Primitive readChar)
  , (mkId "writeChar", Ext () $ Primitive writeChar)
  , (mkId "closeHandle",   Ext () $ Primitive closeHandle)
  , (mkId "showChar",
        Ext () $ Primitive $ \(CharLiteral c) -> return $ StringLiteral $ RT.showChar c)
  , (mkId "charToInt",
        Ext () $ Primitive $ \(CharLiteral c) -> return $ NumInt $ RT.charToInt c)
  , (mkId "charFromInt",
        Ext () $ Primitive $ \(NumInt c) -> return $ CharLiteral $ RT.charFromInt c)
  , (mkId "stringAppend",
        Ext () $ Primitive $ \(StringLiteral s) -> return $
          Ext () $ Primitive $ \(StringLiteral t) -> return $ StringLiteral $ s `RT.stringAppend` t)
  , ( mkId "stringUncons"
    , Ext () $ Primitive $ \(StringLiteral s) -> return $ case uncons s of
        Just (c, s) -> Constr () (mkId "Some") [Constr () (mkId ",") [CharLiteral c, StringLiteral s]]
        Nothing     -> Constr () (mkId "None") []
    )
  , ( mkId "stringCons"
    , Ext () $ Primitive $ \(CharLiteral c) -> return $
        Ext () $ Primitive $ \(StringLiteral s) -> return $ StringLiteral (cons c s)
    )
  , ( mkId "stringUnsnoc"
    , Ext () $ Primitive $ \(StringLiteral s) -> return $ case unsnoc s of
        Just (s, c) -> Constr () (mkId "Some") [Constr () (mkId ",") [StringLiteral s, CharLiteral c]]
        Nothing     -> Constr () (mkId "None") []
    )
  , ( mkId "stringSnoc"
    , Ext () $ Primitive $ \(StringLiteral s) -> return $
        Ext () $ Primitive $ \(CharLiteral c) -> return $ StringLiteral (snoc s c)
    )
  , (mkId "isEOF", Ext () $ Primitive $ \(Ext _ (Handle h)) -> return $ Ext () $ PureWrapper $ do
        b <- SIO.hIsEOF h
        let boolflag =
             if b then Constr () (mkId "True") [] else Constr () (mkId "False") []
        return . Val nullSpan () False $ Constr () (mkId ",") [Ext () $ Handle h, boolflag])
  , (mkId "forkLinear", Ext () $ PrimitiveClosure forkLinear)
  , (mkId "forkLinear'", Ext () $ PrimitiveClosure forkLinear')
  , (mkId "forkNonLinear", Ext () $ PrimitiveClosure forkNonLinear)
  , (mkId "forkReplicate", Ext () $ PrimitiveClosure forkReplicate)
  , (mkId "forkReplicateExactly", Ext () $ PrimitiveClosure forkReplicateExactly)
  , (mkId "forkMulticast", Ext () $ PrimitiveClosure forkMulticast)
  , (mkId "fork",    Ext () $ PrimitiveClosure forkRep)
  , (mkId "recv",    Ext () $ Primitive recv)
  , (mkId "send",    Ext () $ Primitive send)
  , (mkId "selectLeft",   Ext () $ Primitive selectLeft)
  , (mkId "selectRight",  Ext () $ Primitive selectRight)
  , (mkId "offer",        Ext () $ PrimitiveClosure offer)
  , (mkId "close",    Ext () $ Primitive close)
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
  , (mkId "reveal",  Ext () $ Primitive reveal)
  , (mkId "trustedBind",    Ext () $ PrimitiveClosure trustedBind)
  , (mkId "newFloatArray",  Ext () $ Primitive newFloatArray)
  , (mkId "lengthFloatArray",  Ext () $ Primitive lengthFloatArray)
  , (mkId "readFloatArray",  Ext () $ Primitive readFloatArray)
  , (mkId "writeFloatArray",  Ext () $ Primitive writeFloatArray)
  , (mkId "newFloatArrayI",  Ext () $ Primitive newFloatArrayI)
  , (mkId "lengthFloatArrayI",  Ext () $ Primitive lengthFloatArrayI)
  , (mkId "readFloatArrayI",  Ext () $ Primitive readFloatArrayI)
  , (mkId "writeFloatArrayI",  Ext () $ Primitive writeFloatArrayI)
  , (mkId "deleteFloatArray", Ext () $ Primitive deleteFloatArray)
  -- Additive conjunction (linear logic)
  , (mkId "with", Ext () $ Primitive $ \v -> return $ Ext () $ Primitive $ \w -> return $ Constr () (mkId "&") [v, w])
  , (mkId "projL", Ext () $ Primitive $ \(Constr () (Id "&" "&") [v, w]) -> return $ v)
  , (mkId "projR", Ext () $ Primitive $ \(Constr () (Id "&" "&") [v, w]) -> return $ w)
  ]
  where
    forkLinear :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    forkLinear ctxt e = case e of
      Abs{} -> do c <- newChan
                  _ <- C.forkIO $ void $ evalIn ctxt (App nullSpan () False (valExpr e)
                                                       (valExpr $ Ext () $ Chan c))
                  return $ Ext () $ Chan (dualEndpoint c)
      _oth -> error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    forkLinear' :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    forkLinear' ctxt e = case e of
      Abs{} -> do c <- newChan
                  _ <- C.forkIO $ void $ evalIn ctxt (App nullSpan () False
                                                      (valExpr e)
                                                      (valExpr $ Promote () $ valExpr $ Ext () $ Chan c))
                  return $ Ext () $ Chan (dualEndpoint c)
      _oth -> error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    forkNonLinear :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    forkNonLinear ctxt e = case e of
      Abs{} -> do c <- newChan
                  _ <- C.forkIO $ void $ evalIn ctxt (App nullSpan () False
                                                      (valExpr e)
                                                      (valExpr $ Promote () $ valExpr $ Ext () $ Chan c))
                  return $ Promote () $ valExpr $ Ext () $ Chan (dualEndpoint c)
      _oth -> error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    forkMulticast :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    forkMulticast ctxt f@(Abs{}) = return $ Ext () $ Primitive $ \n -> do
          -- Create initial channel that goes to the broadcaster
          initChan <- newChan
          _  <- C.forkIO $ void $
                -- Forked process
                evalIn ctxt (App nullSpan () False
                                (valExpr f)
                                (valExpr $ Ext () $ Chan (dualEndpoint initChan)))
          -- receiver channels
          interChan <- newChan
          receiverChans <- mapM (const (dupChan interChan)) [1..(natToInt n)]
          -- forwarder
          _ <- C.forkIO $ void $ SIO.fixIO $ const $ do
                e <- readChan initChan
                case e of
                  Promote _ (Val _ _ _ v) -> writeChan interChan v
                  _ -> error $ "Bug in Granule. Multicast forwarder got non-boxed value " ++ show e
          -- return receiver chans vector
          return $ buildVec (map dualEndpoint receiverChans) id

    forkMulticast _ e = error $ "Bug in Granule. Trying to forkMulticate: " <> prettyDebug e

    forkReplicateExactly :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    forkReplicateExactly = forkReplicateCore id

    forkReplicate :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    forkReplicate = forkReplicateCore (\x -> Promote () (Val nullSpanNoFile () False x))

    forkReplicateCore :: (?globals :: Globals) => (RValue -> RValue) -> Ctxt RValue -> RValue -> IO RValue
    forkReplicateCore wrapper ctxt (Promote _ (Val _ _ _ f@Abs{})) =
      return $ Ext () $ Primitive $ \n -> do
        -- make the chans
        receiverChans <- mapM (const newChan) [1..(natToInt n)]
        -- fork the waiters which then fork the servers
        _ <- flip mapM receiverChans
              (\receiverChan -> C.forkIO $ void $ do
                -- wait to receive on the main channel
                x <- readChan receiverChan
                () <- putbackChan receiverChan x

                C.forkIO $ void $
                   evalIn ctxt (App nullSpan () False
                                (valExpr f)
                                (valExpr $ Ext () $ Chan receiverChan)))

        return $ buildVec (map dualEndpoint receiverChans) wrapper

    forkReplicateCore _ _ e = error $ "Bug in Granule. Trying to forkReplicate: " <> prettyDebug e


    forkRep :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    forkRep ctxt e = case e of
      Abs{} -> return $ diamondConstr $ do
        c <- newChan
        _ <- C.forkIO $ void $ evalIn ctxt (App nullSpan () False
                                            (valExpr e)
                                            (valExpr $ Promote () $ valExpr $ Ext () $ Chan c))
        return $ valExpr $ Promote () $ valExpr $ Ext () $ Chan (dualEndpoint c)
      _oth -> error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    uniqueReturn :: RValue -> IO RValue
    uniqueReturn (Nec () v) =
      case v of
        (Val nullSpan () False (Ext () (Runtime fa))) -> do
          borrowed <- borrowFloatArraySafe fa
          return $ Promote () (Val nullSpan () False (Ext () (Runtime borrowed)))
        _otherwise -> return $ Promote () v
    uniqueReturn v = error $ "Bug in Granule. Can't borrow a non-unique: " <> prettyDebug v

    uniqueBind :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    uniqueBind ctxt f = return $ Ext () $ Primitive $ \(Promote () v) ->
      case v of
        (Val nullSpan () False (Ext () (Runtime fa))) -> do
          copy <- copyFloatArraySafe fa
          evalIn ctxt
              (App nullSpan () False
                (Val nullSpan () False f)
                (Val nullSpan () False (Nec () (Val nullSpan () False (Ext () (Runtime copy))))))
        _otherwise -> do
          evalIn ctxt
            (App nullSpan () False
             (Val nullSpan () False f)
             (Val nullSpan () False (Nec () v)))

    reveal :: RValue -> IO RValue
    reveal (Nec () v) = return $ Promote () v
    reveal v = error $ "Bug in Granule. Can't reveal a public: " <> prettyDebug v

    trustedBind :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    trustedBind ctxt f = return $ Ext () $ Primitive $ \(Promote () v) -> return $
      case v of
        (Val nullSpan () False (Ext () (Runtime fa))) ->
          let copy = copyFloatArray' fa in
          unsafePerformIO $ evalIn ctxt
              (App nullSpan () False
                (Val nullSpan () False f)
                (Val nullSpan () False (Nec () (Val nullSpan () False (Ext () (Runtime copy))))))
        _otherwise ->
          unsafePerformIO $ evalIn ctxt
            (App nullSpan () False
             (Val nullSpan () False f)
             (Val nullSpan () False (Nec () v)))

    uniquePush :: RValue -> IO RValue
    uniquePush (Nec () (Val nullSpan () False (Constr () (Id "," ",") [x, y])))
     = return $ Constr () (mkId ",") [Nec () (Val nullSpan () False x), Nec () (Val nullSpan () False y)]
    uniquePush v = error $ "Bug in Granule. Can't push through a non-unique: " <> prettyDebug v

    uniquePull :: RValue -> IO RValue
    uniquePull (Constr () (Id "," ",") [Nec () (Val nullSpan () False x), Nec () (Val _ () False y)])
      = return $ Nec () (Val nullSpan () False (Constr () (mkId ",") [x, y]))
    uniquePull v = error $ "Bug in Granule. Can't pull through a non-unique: " <> prettyDebug v

    recv :: (?globals :: Globals) => RValue -> IO RValue
    recv (Ext _ (Chan c)) = do
      x <- readChan c
      return $ Constr () (mkId ",") [x, Ext () $ Chan c]
    recv e = error $ "Bug in Granule. Trying to receive from: " <> prettyDebug e

    send :: (?globals :: Globals) => RValue -> IO RValue
    send (Ext _ (Chan c)) = return $ Ext () $ Primitive
      (\v -> do writeChan c v
                return $ Ext () $ Chan c)
    send e = error $ "Bug in Granule. Trying to send from: " <> prettyDebug e

    selectLeft :: (?globals :: Globals) => RValue -> IO RValue
    selectLeft (Ext _ (Chan c)) = do
      writeChan c (Constr () (mkId "LeftTag") [])
      return $ Ext () $ Chan c
    selectLeft e = error $ "Bug in Granule. Trying to selectLeft from: " <> prettyDebug e

    selectRight :: (?globals :: Globals) => RValue -> IO RValue
    selectRight (Ext _ (Chan c)) = do
      writeChan c (Constr () (mkId "RightTag") [])
      return $ Ext () $ Chan c
    selectRight e = error $ "Bug in Granule. Trying to selectLeft from: " <> prettyDebug e

    offer :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    offer ctxt f = return $ Ext () $ Primitive
      (\g -> return $ Ext () $ Primitive
        (\c ->
          case c of
            (Ext _ (Chan c)) -> do
              x <- readChan c
              case x of
                (Constr () (internalName -> "LeftTag") _) ->
                  evalIn ctxt (App nullSpan () False (Val nullSpan () False f) (valExpr $ Ext () $ Chan c))
                (Constr () (internalName -> "RightTag") _) ->
                  evalIn ctxt (App nullSpan () False (Val nullSpan () False g) (valExpr $ Ext () $ Chan c))
                x -> error $ "Bug in Granule. Offer got tag: " <> prettyDebug x
            _ -> error $ "Bug in Granule. Offer got supposed channel: " <> prettyDebug c))
    close :: RValue -> IO RValue
    close (Ext _ (Chan c)) = return $ Constr () (mkId "()") []
    close rval = error "Runtime exception: trying to close a value which is not a channel"

    grecv :: (?globals :: Globals) => RValue -> IO RValue
    grecv (Ext _ (Chan c)) = return $ diamondConstr $ do
      x <- readChan c
      return $ valExpr $ Constr () (mkId ",") [x, Ext () $ Chan c]
    grecv e = error $ "Bug in Granule. Trying to receive from: " <> prettyDebug e

    gsend :: (?globals :: Globals) => RValue -> IO RValue
    gsend (Ext _ (Chan c)) = return $ Ext () $ Primitive
      (\v -> return $ diamondConstr $ do
         writeChan c v
         return $ valExpr $ Ext () $ Chan c)
    gsend e = error $ "Bug in Granule. Trying to send from: " <> prettyDebug e

    gclose :: RValue -> IO RValue
    gclose (Ext _ (Chan c)) = return $ diamondConstr $ return $ valExpr $ Constr () (mkId "()") []
    gclose rval = error "Runtime exception: trying to close a value which is not a channel"

    openHandle :: RValue -> IO RValue
    openHandle (Constr _ m []) = return $
      Ext () $ Primitive (\x -> return $ diamondConstr (
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

    writeChar :: RValue -> IO RValue
    writeChar (Ext _ (Handle h)) = return $
      Ext () $ Primitive (\c -> return $ diamondConstr (
        case c of
          (CharLiteral c) -> do
            SIO.hPutChar h c
            return $ valExpr $ Ext () $ Handle h
          _ -> error $ "Runtime exception: trying to put a non character value"))
    writeChar _ = error $ "Runtime exception: trying to put from a non handle value"

    readChar :: RValue -> IO RValue
    readChar (Ext _ (Handle h)) = return $ diamondConstr $ do
          c <- SIO.hGetChar h
          return $ valExpr (Constr () (mkId ",") [Ext () $ Handle h, CharLiteral c])
    readChar h = error $ "Runtime exception: trying to get from a non handle value" <> prettyDebug h

    closeHandle :: RValue -> IO RValue
    closeHandle (Ext _ (Handle h)) = return $ diamondConstr $ do
         SIO.hClose h
         return $ valExpr (Constr () (mkId "()") [])
    closeHandle _ = error "Runtime exception: trying to close a non handle value"

    newFloatArray :: RValue -> IO RValue
    newFloatArray = \(NumInt i) -> do
      arr <- RT.newFloatArraySafe i
      return $ Nec () $ Val nullSpan () False $ Ext () $ Runtime arr

    newFloatArrayI :: RValue -> IO RValue
    newFloatArrayI = \(NumInt i) -> do
      arr <- RT.newFloatArrayISafe i
      return $ Ext () $ Runtime arr

    readFloatArray :: RValue -> IO RValue
    readFloatArray = \(Nec () (Val _ _ _ (Ext () (Runtime fa)))) -> return $ Ext () $ Primitive $ \(NumInt i) -> do
      (e,fa') <- RT.readFloatArraySafe fa i
      return $ Constr () (mkId ",") [NumFloat e, Nec () (Val nullSpan () False $ Ext () $ Runtime fa')]

    readFloatArrayI :: RValue -> IO RValue
    readFloatArrayI = \(Ext () (Runtime fa)) -> return $ Ext () $ Primitive $ \(NumInt i) -> do
      (e,fa') <- RT.readFloatArrayISafe fa i
      return $ Constr () (mkId ",") [NumFloat e, Ext () $ Runtime fa']

    lengthFloatArray :: RValue -> IO RValue
    lengthFloatArray = \(Nec () (Val _ _ _ (Ext () (Runtime fa)))) ->
      let (e,fa') = RT.lengthFloatArray fa
      in return $ Constr () (mkId ",") [NumInt e, Nec () (Val nullSpan () False $ Ext () $ Runtime fa')]

    lengthFloatArrayI :: RValue -> IO RValue
    lengthFloatArrayI = \(Ext () (Runtime fa)) ->
      let (e,fa') = RT.lengthFloatArray fa
      in return $ Constr () (mkId ",") [NumInt e, Ext () $ Runtime fa']

    writeFloatArray :: RValue -> IO RValue
    writeFloatArray = \(Nec _ (Val _ _ _ (Ext _ (Runtime fa)))) -> return $
      Ext () $ Primitive $ \(NumInt i) -> return $
        Ext () $ Primitive $ \(NumFloat v) -> do
          arr <- RT.writeFloatArraySafe fa i v
          return $ Nec () $ Val nullSpan () False $ Ext () $ Runtime arr

    writeFloatArrayI :: RValue -> IO RValue
    writeFloatArrayI = \(Ext () (Runtime fa)) -> return $
      Ext () $ Primitive $ \(NumInt i) -> return $
      Ext () $ Primitive $ \(NumFloat v) -> do
        arr <- RT.writeFloatArrayISafe fa i v
        return $ Ext () $ Runtime arr

    deleteFloatArray :: RValue -> IO RValue
    deleteFloatArray = \(Nec _ (Val _ _ _ (Ext _ (Runtime fa)))) -> do
      deleteFloatArraySafe fa
      return $ Constr () (mkId "()") []

-- Convert a Granule value representation of `N n` type into an Int
natToInt :: RValue -> Int
natToInt (Constr () c [])  | internalName c == "Z" =  0
natToInt (Constr () c [v]) | internalName c == "S" =  1 + natToInt v
natToInt k = error $ "Bug in Granule. Trying to convert a N but got value " <> show k

-- Convert a list of channels into a granule `Vec n (LChan ...)` value.
buildVec :: [BinaryChannel ()] -> (RValue -> RValue) -> RValue
buildVec [] _ = Constr () (mkId "Nil") []
buildVec (c:cs) f = Constr () (mkId "Cons") [f $ Ext () $ Chan c, buildVec cs f]

evalDefs :: (?globals :: Globals) => Ctxt RValue -> [Def (Runtime ()) ()] -> IO (Ctxt RValue)
evalDefs ctxt [] = return ctxt
evalDefs ctxt (Def _ var _ _ (EquationList _ _ _ [Equation _ _ _ rf [] e]) _ : defs) = do
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
  toRuntimeRep (Def s i rf spec eqs tys) = Def s i rf Nothing (toRuntimeRep eqs) tys

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
  toRuntimeRep (Unpack s a rf tyVar var e1 e2) = Unpack s a rf tyVar var (toRuntimeRep e1) (toRuntimeRep e2)
  toRuntimeRep (Hole s a rf vs hs) = Hole s a rf vs hs

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
  toRuntimeRep (Pack s a ty e var k ty') = Pack s a ty (toRuntimeRep e) var k ty'

eval :: (?globals :: Globals) => AST () () -> IO (Maybe RValue)
eval = evalAtEntryPoint (mkId entryPoint)

evalAtEntryPoint :: (?globals :: Globals) => Id -> AST () () -> IO (Maybe RValue)
evalAtEntryPoint entryPoint (AST dataDecls defs _ _ _) = do
    bindings <- evalDefs builtIns (map toRuntimeRep defs)
    case lookup entryPoint bindings of
      Nothing             -> return Nothing
      -- Evaluate inside a promotion of pure if its at the top-level
      Just (Pure _ e)     -> fmap Just (evalIn bindings e)
      Just (Ext _ (PureWrapper e)) -> do
        eExpr <- e
        fmap Just (evalIn bindings eExpr)
      Just (Promote _ e) -> fmap Just (evalIn bindings e)
      Just (Nec _ e)     -> fmap Just (evalIn bindings e)
      -- ... or a regular value came out of the interpreter
      Just val           -> return $ Just val

-- Predicate on whether a term is going to be reducible under the big
-- step semantics (either reduction scheme)
isReducible :: Expr ev a -> Bool
isReducible (Val _ _ _ (Var _ _)) = True
isReducible (Val _ _ _ _)    = False
isReducible (Hole _ _ _ _ _) = False
isReducible _              = True
