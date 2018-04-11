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
import Control.Exception (try)
import Control.Monad.State
import System.Console.Haskeline
import System.Console.Haskeline.MonadException()
import Repl.ReplError
import System.FilePath.Glob (glob)
import Utils
import Syntax.Pretty
import Syntax.Expr
import Syntax.Parser
import Repl.ReplParser
import Checker.Checker
import Eval
import qualified Control.Monad.Except as Ex

type REPLStateIO a  = StateT ([Def],[FilePath], M.Map String (Def, [String])) (Ex.ExceptT ReplError IO) a

instance MonadException m => MonadException (StateT ([Def],[FilePath], M.Map String (Def, [String])) m) where
    controlIO f = StateT $ \s -> controlIO $ \(RunIO run) -> let
                    run' = RunIO (fmap (StateT . const) . run . flip runStateT s)
                    in fmap (flip runStateT s) $ f run'

instance MonadException m => MonadException (Ex.ExceptT e m) where
  controlIO f = Ex.ExceptT $ controlIO $ \(RunIO run) -> let
                  run' = RunIO (fmap Ex.ExceptT . run . Ex.runExceptT)
                  in fmap Ex.runExceptT $ f run'

liftIO' :: IO a -> REPLStateIO a
liftIO' = lift.lift

processFilesREPL :: [FilePath] -> (FilePath -> REPLStateIO a) -> REPLStateIO [[a]]
processFilesREPL globPatterns f = forM globPatterns $ (\p -> do
    filePaths <- liftIO $ glob p
    case filePaths of
        [] -> lift $ Ex.throwError (FilePathError p)
        _ -> forM filePaths f)


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
  (adt,f,m) <- get
  if M.member (pretty id) m
  then Ex.throwError (TermInContext (pretty id))
  else put $ (adt,f,M.insert (pretty id) (def,(makeUnique $ extractFreeVars id (freeVars def))) m)

loadInQueue adt'@(ADT _ _ _ _ _) = do
  (adt,f,m) <- get
  put ((adt':adt),f,m)


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


handleCMD :: (?globals::Globals) => String -> REPLStateIO ()
handleCMD "" = Ex.return ()
handleCMD s =
   case (parseLine s) of
    Right l -> handleLine l
    Left msg -> liftIO $ putStrLn msg

  where
    handleLine :: (?globals::Globals) => REPLExpr -> REPLStateIO ()
    handleLine DumpState = do
      (adt,f,dict) <- get
      liftIO $ print $ dumpStateAux dict

    handleLine (LoadFile ptr) = do
      put ([],ptr,M.empty)
      ecs <- processFilesREPL ptr (let ?globals = ?globals in readToQueue)
      return ()

    handleLine (AddModule ptr) = do
      ecs <- processFilesREPL ptr (let ?globals = ?globals in readToQueue)
      return ()

    handleLine Reload = do
      (adt,f,_) <- get
      put (adt,f, M.empty)
      ecs <- processFilesREPL f (let ?globals = ?globals in readToQueue)
      return ()

    handleLine (CheckType trm) = do
      (adt,_,m) <- get
      let cked = buildAST trm m
      case cked of
        []  -> Ex.throwError (TermNotInContext trm)
        ast -> do
          checked <- liftIO' $ check (adt++ast)
          case checked of
            Ok -> liftIO $ putStrLn (printType trm m)
            Failed -> Ex.throwError (TypeCheckError trm)

    handleLine (Eval ev) = do
      (adt,fp,m) <- get
      let cked = buildAST ev m
      case cked of
        [] -> undefined -- if can eval without full function def, do it here
        ast -> do
          checked <- liftIO' $ check (adt++ast)
          case checked of
            Ok -> do
              result <- liftIO' $ try $ eval (adt++ast)
              case result of
                Left e -> Ex.throwError (EvalError e)
                Right Nothing -> liftIO $ putStrLn "here"
                Right (Just result) -> liftIO $ putStrLn (pretty result)

      -- pev <- liftIO' $ try $ parseDefs ev
      -- case pev of
      --   Right ast -> do
      --         checked <-  liftIO' $ check ast
      --         case checked of
      --           Ok -> do
      --             result <- eval ast
      --           Failed -> undefined
      --   Left e -> Ex.throwError (ParseError e)


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

repl :: IO ()
repl = runInputT defaultSettings (loop ([],[],M.empty))
   where
       loop :: ([Def],[FilePath] ,M.Map String (Def, [String])) -> InputT IO ()
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
