-- Granule interpreter
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

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

import qualified Control.Concurrent as C (forkIO)
import qualified Control.Concurrent.Chan as CC (newChan, writeChan, readChan, Chan)

import System.IO (hFlush, stdout)
import qualified System.IO as SIO (Handle, hGetChar, hPutChar, hClose, openFile, IOMode, isEOF)

type RValue = Value (Runtime ()) ()
type RExpr = Expr (Runtime ()) ()

-- | Runtime values only used in the interpreter
data Runtime a =
  -- | Primitive functions (builtins)
    Primitive ((Value (Runtime a) a) -> IO (Value (Runtime a) a))

  -- | Primitive operations that also close over the context
  | PrimitiveClosure (Ctxt (Value (Runtime a) a) -> (Value (Runtime a) a) -> IO (Value (Runtime a) a))

  -- | File handler
  | Handle SIO.Handle

  -- | Channels
  | Chan (CC.Chan (Value (Runtime a) a))

instance Show (Runtime a) where
  show (Chan _) = "Some channel"
  show (Primitive _) = "Some primitive"
  show (PrimitiveClosure _) = "Some primitive closure"
  show (Handle _) = "Some handle"

instance Show (Runtime a) => Pretty (Runtime a) where
  prettyL _ = show

evalBinOp :: String -> RValue -> RValue -> RValue
evalBinOp "+" (NumInt n1) (NumInt n2) = NumInt (n1 + n2)
evalBinOp "*" (NumInt n1) (NumInt n2) = NumInt (n1 * n2)
evalBinOp "-" (NumInt n1) (NumInt n2) = NumInt (n1 - n2)
evalBinOp "+" (NumFloat n1) (NumFloat n2) = NumFloat (n1 + n2)
evalBinOp "*" (NumFloat n1) (NumFloat n2) = NumFloat (n1 * n2)
evalBinOp "-" (NumFloat n1) (NumFloat n2) = NumFloat (n1 - n2)
evalBinOp "==" (NumInt n) (NumInt m) = Constr () (mkId . show $ (n == m)) []
evalBinOp "<=" (NumInt n) (NumInt m) = Constr () (mkId . show $ (n <= m)) []
evalBinOp "<" (NumInt n) (NumInt m)  = Constr () (mkId . show $ (n < m)) []
evalBinOp ">=" (NumInt n) (NumInt m) = Constr () (mkId . show $ (n >= m)) []
evalBinOp ">" (NumInt n) (NumInt m)  = Constr () (mkId . show $ (n > m)) []
evalBinOp "==" (NumFloat n) (NumFloat m) = Constr () (mkId . show $ (n == m)) []
evalBinOp "<=" (NumFloat n) (NumFloat m) = Constr () (mkId . show $ (n <= m)) []
evalBinOp "<" (NumFloat n) (NumFloat m)  = Constr () (mkId . show $ (n < m)) []
evalBinOp ">=" (NumFloat n) (NumFloat m) = Constr () (mkId . show $ (n >= m)) []
evalBinOp ">" (NumFloat n) (NumFloat m)  = Constr () (mkId . show $ (n > m)) []
evalBinOp op v1 v2 = error $ "Unknown operator " <> op
                             <> " on " <> show v1 <> " and " <> show v2

-- Call-by-value big step semantics
evalIn :: (?globals :: Globals) => Ctxt RValue -> RExpr -> IO RValue

evalIn _ (Val s _ (Var _ v)) | internalName v == "read" = do
    putStr "> "
    hFlush stdout
    val <- Text.getLine
    return $ Pure () (Val s () (StringLiteral val))

evalIn _ (Val s _ (Var _ v)) | internalName v == "readInt" = do
    putStr "> "
    hFlush stdout
    val <- readLn
    return $ Pure () (Val s () (NumInt val))

evalIn _ (Val _ _ (Abs _ p t e)) = return $ Abs () p t e

evalIn ctxt (App s _ e1 e2) = do
    v1 <- evalIn ctxt e1
    case v1 of
      (Ext _ (Primitive k)) -> do
        v2 <- evalIn ctxt e2
        k v2

      Abs _ p _ e3 -> do
        p <- pmatchTop ctxt [(p, e3)] e2
        case p of
          Just (e3, bindings) -> evalIn ctxt (applyBindings bindings e3)
          _ -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in application at " <> pretty s

      Constr _ c vs -> do
        v2 <- evalIn ctxt e2
        return $ Constr () c (vs <> [v2])

      _ -> error $ show v1
      -- _ -> error "Cannot apply value"

evalIn ctxt (Binop _ _ op e1 e2) = do
     v1 <- evalIn ctxt e1
     v2 <- evalIn ctxt e2
     return $ evalBinOp op v1 v2

evalIn ctxt (LetDiamond s _ p _ e1 e2) = do
     v1 <- evalIn ctxt e1
     case v1 of
       Pure _ e -> do
         v1' <- evalIn ctxt e
         p  <- pmatch ctxt [(p, e2)] v1'
         case p of
           Just (e2, bindings) -> evalIn ctxt (applyBindings bindings e2)
           Nothing -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in let at " <> pretty s
       other -> fail $ "Runtime exception: Expecting a diamonad value bug got: "
                      <> prettyDebug other

{-
-- Hard-coded 'scale', removed for now


evalIn _ (Val _ (Var v)) | internalName v == "scale" = return
  (Abs (PVar nullSpan $ mkId " x") Nothing (Val nullSpan
    (Abs (PVar nullSpan $ mkId " y") Nothing (
      letBox nullSpan (PVar nullSpan $ mkId " ye")
         (Val nullSpan (Var (mkId " y")))
         (Binop nullSpan
           "*" (Val nullSpan (Var (mkId " x"))) (Val nullSpan (Var (mkId " ye"))))))))
-}

evalIn ctxt (Val _ _ (Var _ x)) =
    case lookup x ctxt of
      Just val@(Ext _ (PrimitiveClosure f)) -> return $ Ext () $ Primitive (f ctxt)
      Just val -> return val
      Nothing  -> fail $ "Variable '" <> sourceName x <> "' is undefined in context."

evalIn ctxt (Val s _ (Pure _ e)) = do
  v <- evalIn ctxt e
  return $ Pure () (Val s () v)

evalIn _ (Val _ _ v) = return v

evalIn ctxt (Case _ _ guardExpr cases) = do
    p <- pmatchTop ctxt cases guardExpr
    case p of
      Just (ei, bindings) -> evalIn ctxt (applyBindings bindings ei)
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
  => Ctxt RValue
  -> [(Pattern (), RExpr)]
  -> RExpr
  -> IO (Maybe (RExpr, Ctxt RExpr))

pmatchTop ctxt ((PBox _ _ (PVar _ _ var), branchExpr):_) guardExpr = do
  Promote _ e <- evalIn ctxt guardExpr
  return (Just (subst e var branchExpr, []))

pmatchTop ctxt ((PBox _ _ (PWild _ _), branchExpr):_) guardExpr = do
  Promote _ _ <- evalIn ctxt guardExpr
  return (Just (branchExpr, []))

pmatchTop ctxt ps guardExpr = do
  val <- evalIn ctxt guardExpr
  pmatch ctxt ps val

pmatch ::
  (?globals :: Globals)
  => Ctxt RValue
  -> [(Pattern (), RExpr)]
  -> RValue
  -> IO (Maybe (RExpr, Ctxt RExpr))
pmatch _ [] _ =
   return Nothing

pmatch _ ((PWild _ _, e):_)  _ =
   return $ Just (e, [])

pmatch ctxt ((PConstr _ _ s innerPs, e):ps) (Constr _ s' vs) | s == s' = do
   matches <- zipWithM (\p v -> pmatch ctxt [(p, e)] v) innerPs vs
   case sequence matches of
     Just ebindings -> return $ Just (e, concat $ map snd ebindings)
     Nothing        -> pmatch ctxt ps (Constr () s' vs)

pmatch _ ((PVar _ _ var, e):_) val =
   return $ Just (e, [(var, Val nullSpan () val)])

pmatch ctxt ((PBox _ _ p, e):ps) (Promote _ e') = do
  v <- evalIn ctxt e'
  match <- pmatch ctxt [(p, e)] v
  case match of
    Just (_, bindings) -> return $ Just (e, bindings)
    Nothing -> pmatch ctxt ps (Promote () e')

pmatch _ ((PInt _ _ n, e):_)   (NumInt m)   | n == m  =
   return $ Just (e, [])

pmatch _ ((PFloat _ _ n, e):_) (NumFloat m) | n == m =
   return $ Just (e, [])

pmatch ctxt (_:ps) val = pmatch ctxt ps val

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
        return . (Pure ()) . Val nullSpan () $ Constr () (mkId "(,)") [Ext () $ Handle h, boolflag])
  , (mkId "fork",    Ext () $ PrimitiveClosure fork)
  , (mkId "forkRep", Ext () $ PrimitiveClosure forkRep)
  , (mkId "recv",    Ext () $ Primitive recv)
  , (mkId "send",    Ext () $ Primitive send)
  , (mkId "close",   Ext () $ Primitive close)
  ]
  where
    fork :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    fork ctxt e@Abs{} = do
      c <- CC.newChan
      C.forkIO $
         evalIn ctxt (App nullSpan () (valExpr e) (valExpr $ Ext () $ Chan c)) >> return ()
      return $ Pure () $ valExpr $ Ext () $ Chan c
    fork ctxt e = error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    forkRep :: (?globals :: Globals) => Ctxt RValue -> RValue -> IO RValue
    forkRep ctxt e@Abs{} = do
      c <- CC.newChan
      C.forkIO $
         evalIn ctxt (App nullSpan ()
                        (valExpr e)
                        (valExpr $ Promote () $ valExpr $ Ext () $ Chan c)) >> return ()
      return $ Pure () $ valExpr $ Promote () $ valExpr $ Ext () $ Chan c
    forkRep ctxt e = error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    recv :: (?globals :: Globals) => RValue -> IO RValue
    recv (Ext _ (Chan c)) = do
      x <- CC.readChan c
      return $ Pure () $ valExpr $ Constr () (mkId "(,)") [x, Ext () $ Chan c]
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

    hGetChar :: RValue -> IO RValue
    hGetChar (Ext _ (Handle h)) = do
          c <- SIO.hGetChar h
          return $ Pure () $ valExpr (Constr () (mkId "(,)") [Ext () $ Handle h, CharLiteral c])
    hGetChar _ = error $ "Runtime exception: trying to get from a non handle value"

    hClose :: RValue -> IO RValue
    hClose (Ext _ (Handle h)) = do
         SIO.hClose h
         return $ Pure () $ valExpr (Constr () (mkId "()") [])
    hClose _ = error $ "Runtime exception: trying to close a non handle value"

evalDefs :: (?globals :: Globals) => Ctxt RValue -> [Def (Runtime ()) ()] -> IO (Ctxt RValue)
evalDefs ctxt [] = return ctxt
evalDefs ctxt (Def _ var [Equation _ _ [] e] _ : defs) = do
    val <- evalIn ctxt e
    case extend ctxt var val of
      Some ctxt -> evalDefs ctxt defs
      None msgs -> error $ unlines msgs
evalDefs ctxt (d : defs) = do
    let d' = desugar d
    evalDefs ctxt (d' : defs)

-- Maps an AST from the parser into the interpreter version with runtime values
class RuntimeRep t where
  toRuntimeRep :: t () () -> t (Runtime ()) ()

instance RuntimeRep Def where
  toRuntimeRep (Def s i eqs tys) = Def s i (map toRuntimeRep eqs) tys

instance RuntimeRep Equation where
  toRuntimeRep (Equation s a ps e) = Equation s a ps (toRuntimeRep e)

instance RuntimeRep Expr where
  toRuntimeRep (Val s a v) = Val s a (toRuntimeRep v)
  toRuntimeRep (App s a e1 e2) = App s a (toRuntimeRep e1) (toRuntimeRep e2)
  toRuntimeRep (Binop s a o e1 e2) = Binop s a o (toRuntimeRep e1) (toRuntimeRep e2)
  toRuntimeRep (LetDiamond s a p t e1 e2) = LetDiamond s a p t (toRuntimeRep e1) (toRuntimeRep e2)
  toRuntimeRep (Case s a e ps) = Case s a (toRuntimeRep e) (map (\(p, e) -> (p, toRuntimeRep e)) ps)

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

eval :: (?globals :: Globals) => AST () () -> IO (Maybe RValue)
eval (AST dataDecls defs) = do
    bindings <- evalDefs builtIns (map toRuntimeRep defs)
    case lookup (mkId "main") bindings of
      Nothing -> return Nothing
      -- Evaluate inside a promotion of pure if its at the top-level
      Just (Pure _ e)    -> fmap Just (evalIn bindings e)
      Just (Promote _ e) -> fmap Just (evalIn bindings e)
      -- ... or a regular value came out of the interpreter
      Just val           -> return $ Just val
