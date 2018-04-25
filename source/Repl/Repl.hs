{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

module Repl.Repl where

import System.FilePath
import qualified Data.Map as M
import qualified Checker.Monad as Mo
import Control.Exception (try)
import Control.Monad.State
import Control.Monad.Trans.Maybe
import System.Console.Haskeline
import System.Console.Haskeline.MonadException()
import Repl.ReplError
import System.FilePath.Glob (glob, compile, globDir1)
import Utils
import Syntax.Pretty
import Syntax.Expr
import Syntax.Parser
import Syntax.Lexer
import Repl.ReplParser
import Checker.Checker
import Eval
import Context
import qualified Control.Monad.Except as Ex

type ReplPATH = [FilePath]
type ADT = [Def]
type FreeVarGen = Int
type REPLStateIO a  = StateT (FreeVarGen,ReplPATH,ADT,[FilePath], M.Map String (Def, [String])) (Ex.ExceptT ReplError IO) a

instance MonadException m => MonadException (StateT (FreeVarGen,ReplPATH,ADT,[FilePath], M.Map String (Def, [String])) m) where
    controlIO f = StateT $ \s -> controlIO $ \(RunIO run) -> let
                    run' = RunIO (fmap (StateT . const) . run . flip runStateT s)
                    in fmap (flip runStateT s) $ f run'

instance MonadException m => MonadException (Ex.ExceptT e m) where
  controlIO f = Ex.ExceptT $ controlIO $ \(RunIO run) -> let
                  run' = RunIO (fmap Ex.ExceptT . run . Ex.runExceptT)
                  in fmap Ex.runExceptT $ f run'

eval' :: (?globals :: Globals) =>Int -> AST -> IO (Maybe Value)
eval' val defs = do
    bindings <- evalDefs builtIns defs
    case lookup (mkId (" repl"++(show val))) bindings of
      Nothing -> return Nothing
      Just (Pure e)    -> fmap Just (evalIn bindings e)
      Just (Promote e) -> fmap Just (evalIn bindings e)
      Just val         -> return $ Just val

liftIO' :: IO a -> REPLStateIO a
liftIO' = lift.lift

processFilesREPL :: [FilePath] -> (FilePath -> REPLStateIO a) -> REPLStateIO [[a]]
processFilesREPL globPatterns f = forM globPatterns $ (\p -> do
    filePaths <- liftIO $ glob p
    case filePaths of
        [] -> lift $ Ex.throwError (FilePathError p)
        _ -> forM filePaths f)

--[] -> lift $ Ex.throwError (FilePathError p)

replPath :: String -> ReplPATH -> IO [[FilePath]]
replPath f rps = do
   let pat = compile f
   forM rps $ (\x -> globDir1 pat x)

searchRP :: [String] -> ReplPATH -> IO [[FilePath]]
searchRP [] rp = return [[]]
searchRP (s:sx) rp =do
   x <- (replPath s rp)
   y <- searchRP sx rp
   return $ x ++ y


readToQueue :: (?globals::Globals) => FilePath -> REPLStateIO ()
readToQueue pth = do
    pf <- liftIO' $ try $ parseDefs =<< readFile pth
    case pf of
      Right ast -> do
            checked <-  liftIO' $ check ast
            case checked of
                Ok -> do
                    forM ast $ \idef -> loadInQueue idef
                    liftIO $ putStrLn $ (takeFileName pth)++" loaded and checked"
                Failed -> Ex.throwError (TypeCheckError pth)
      Left e -> Ex.throwError (ParseError e)



loadInQueue :: (?globals::Globals) => Def -> REPLStateIO  ()
loadInQueue def@(Def _ id exp _ _) = do
  -- liftIO.print $ freeVars def
  -- liftIO.print $ freeVars exp
  (fvg,rp,adt,f,m) <- get
  if M.member (pretty id) m
  then Ex.throwError (TermInContext (pretty id))
  else put $ (fvg,rp,adt,f,M.insert (pretty id) (def,(makeUnique $ extractFreeVars id (freeVars def))) m)

loadInQueue adt'@(ADT _ _ _ _ _) = do
  (fvg,rp,adt,f,m) <- get
  put (fvg,rp,(adt':adt),f,m)


dumpStateAux :: (?globals::Globals) => M.Map String (Def, [String]) -> [String]
dumpStateAux m = pDef (M.toList m)
  where
    pDef :: [(String, (Def, [String]))] -> [String]
    pDef [] = []
    pDef ((k,(v@(Def _ _ _ _ ty),dl)):xs) = ((pretty k)++" : "++(pretty ty)) : pDef xs

extractFreeVars :: Id -> [Id] -> [String]
extractFreeVars _ []     = []
extractFreeVars i (x:xs) = if sourceName x == internalName x && sourceName x /= sourceName i
                           then sourceName x : extractFreeVars i xs
                           else extractFreeVars i xs

makeUnique ::[String] -> [String]
makeUnique []     = []
makeUnique (x:xs) = x : makeUnique (filter (/=x) xs)

buildAST ::String -> M.Map String (Def, [String]) -> [Def]
buildAST t m = let v = M.lookup t m in
                  case v of
                   Nothing -> []
                   Just (def,lid) -> case lid of
                                      []  ->  [def]
                                      ids -> (buildDef ids ++ [def])
                                               where
                                                 buildDef :: [String] -> [Def]
                                                 buildDef [] =  []
                                                 buildDef (x:xs) =  buildDef xs++(buildAST x m)

printType :: (?globals::Globals) => String -> M.Map String (Def, [String]) -> String
printType trm m = let v = M.lookup trm m in
                    case v of
                      Nothing ->""
                      Just (def@(Def _ id _ _ ty),lid) -> (pretty id)++" : "++(pretty ty)

buildForEval :: [Id] -> M.Map String (Def, [String]) -> AST
buildForEval [] _ = []
buildForEval (x:xs) m = buildAST (sourceName x) m ++ buildForEval xs m

synType :: (?globals::Globals) => Expr -> Ctxt TypeScheme -> IO (Maybe (Type, Ctxt Mo.Assumption))
synType exp [] = liftIO $ Mo.evalChecker Mo.initState $ runMaybeT $ synthExpr empty empty Positive exp
synType exp cts = liftIO $ Mo.evalChecker Mo.initState $ runMaybeT $ synthExpr cts empty Positive exp

synTypePlus :: (?globals::Globals) => Expr -> AST -> REPLStateIO Type
synTypePlus exp ast = do
  ty <- liftIO $ synType exp (buildCtxtTS ast)
  case ty of
    Just (t,a) -> return t
    Nothing -> Ex.throwError OtherError'

buildCtxtTS :: (?globals::Globals) => AST -> Ctxt TypeScheme
buildCtxtTS [] = []
buildCtxtTS ((x@(Def _ id _ _ ts)):ast) =  (id,ts) : buildCtxtTS ast
buildCtxtTS (x@(ADT _ _ _ _ _):ast) = buildCtxtTS ast

buildTypeScheme :: (?globals::Globals) => Type -> TypeScheme
buildTypeScheme ty = Forall ((0,0),(0,0)) [] ty

buildDef ::Int -> TypeScheme -> Expr -> Def
buildDef rfv ts ex = Def ((0,0),(0,0)) (mkId (" repl"++(show rfv))) ex [] ts


handleCMD :: (?globals::Globals) => String -> REPLStateIO ()
handleCMD "" = Ex.return ()
handleCMD s =
   case (parseLine s) of
    Right l -> handleLine l
    Left msg -> liftIO $ putStrLn msg

  where
    handleLine :: (?globals::Globals) => REPLExpr -> REPLStateIO ()
    handleLine DumpState = do
      (_,_,adt,f,dict) <- get
      liftIO $ print $ dumpStateAux dict

    handleLine (LoadFile ptr) = do
      (fvg,rp,_,_,_) <- get
      put (fvg,rp,[],ptr,M.empty)
      x <- liftIO' (searchRP ptr rp)
      case concat x of
        [] -> do
          ecs <- processFilesREPL ptr (let ?globals = ?globals in readToQueue)
          return ()
        _ -> do
          ecs <- processFilesREPL (concat x) (let ?globals = ?globals in readToQueue)
          return ()

    handleLine (AddModule ptr) = do
      ecs <- processFilesREPL ptr (let ?globals = ?globals in readToQueue)
      return ()

    handleLine Reload = do
      (fvg,rp,adt,f,_) <- get
      put (fvg,rp,adt,f, M.empty)
      ecs <- processFilesREPL f (let ?globals = ?globals in readToQueue)
      return ()

    handleLine (CheckType trm) = do
      (_,_,adt,_,m) <- get
      let cked = buildAST trm m
      case cked of
        []  -> Ex.throwError (TermNotInContext trm)
        ast -> do
          checked <- liftIO' $ check (adt++ast)
          case checked of
            Ok -> liftIO $ putStrLn (printType trm m)
            Failed -> Ex.throwError (TypeCheckError trm)

    handleLine (Eval ev) = do
        (fvg,rp,adt,fp,m) <- get
        pexp <- liftIO' $ try $ expr $ scanTokens ev
        case pexp of
            Right exp -> do
                let fv = freeVars exp
                case fv of
                    [] -> do -- simple expressions
                        typ <- liftIO $ synType exp []
                        case typ of
                            Just (t,a) -> return ()
                            Nothing -> Ex.throwError (TypeCheckError ev)
                        result <- liftIO' $ try $ evalIn builtIns exp
                        case result of
                            Right r -> liftIO $ putStrLn (pretty r)
                            Left e -> Ex.throwError (EvalError e)
                    _ -> do
                        let ast = buildForEval fv m
                        typer <- synTypePlus exp (adt++ast)
                        let ndef = buildDef fvg (buildTypeScheme typer) exp
                        put ((fvg+1),rp,adt,fp,m)
                        checked <- liftIO' $ check (adt++ast++(ndef:[]))
                        case checked of
                            Ok -> do
                                result <- liftIO' $ try $ eval' fvg (adt++ast++(ndef:[]))
                                case result of
                                    Left e -> Ex.throwError (EvalError e)
                                    Right Nothing -> liftIO $ print "if here fix"
                                    Right (Just result) -> liftIO $ putStrLn (pretty result)
                            Failed -> Ex.throwError (OtherError')
            Left e -> Ex.throwError (ParseError e) --error from parsing (pexp)

helpMenu :: String
helpMenu =
      "-----------------------------------------------------------------------------------\n"++
      "                  The Granule Help Menu                                         \n"++
      "-----------------------------------------------------------------------------------\n"++
      ":help              (:h)  Display the help menu\n"++
      ":quit              (:q)  Quit Granule\n"++
      ":type <term>       (:t)  Display type of term\n"++
      ":dump              (:d)  Display the context\n"++
      ":load <filepath>   (:l)  Load an external file into the context\n"++
      ":module <filepath> (:m)  Add file/module to the current context\n"++
      "-----------------------------------------------------------------------------------"
-- ":unfold <term>     (:u)  Unfold the expression into one without toplevel definition.\n"++
-- ":show <term>       (:s)  Display the Abstract Syntax Type of a term\n"++
defaultReplPath :: [FilePath]
defaultReplPath = ["examples\\","tests\\regression\\good\\"]
repl :: IO ()
repl = runInputT defaultSettings (loop (0,defaultReplPath,[],[],M.empty))
   where
       loop :: (FreeVarGen,ReplPATH,ADT,[FilePath] ,M.Map String (Def, [String])) -> InputT IO ()
       loop st = do
           minput <- getInputLine "Granule> "
           case minput of
               Nothing -> return ()
               Just [] -> loop st
               Just input | input == ":q" || input == ":quit"
                              -> liftIO $ putStrLn "Leaving Granule." >> return ()
                          | input == ":h" || input == ":help"
                              -> (liftIO $ putStrLn helpMenu) >> loop st
                          | otherwise -> do r <- liftIO $ Ex.runExceptT (runStateT (let ?globals = defaultGlobals in handleCMD input) st)
                                            case r of
                                              Right (_,st') -> loop st'
                                              Left err -> do
                                                 liftIO $ print err
                                                 loop st
