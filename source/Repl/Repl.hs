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
import Control.Exception (SomeException, try)
import Control.Monad.State
import System.Console.Haskeline
import System.Console.Haskeline.MonadException()
import Repl.ReplError
import System.Exit
import System.FilePath.Glob (glob)
import Utils
import Syntax.Pretty
import Syntax.Expr
import Syntax.Parser
import Repl.ReplParser
import Checker.Checker
import qualified Control.Monad.Except as Ex

type REPLStateIO a  = StateT (M.Map String Def) (Ex.ExceptT ReplError IO) a

instance MonadException m => MonadException (StateT (M.Map String Def) m) where
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
      Right (ast, maxFreshId) -> do
            let ?globals = ?globals { freshIdCounter = maxFreshId }
            checked <-  liftIO' $ check ast
            case checked of
                Ok -> do
                    forM ast $ \idef -> loadInQueue idef
                    Ex.return ()
                Failed -> Ex.throwError (TypeCheckError pth)
      Left e -> do
            Ex.throwError (ParseError e)


loadInQueue :: Def -> REPLStateIO  ()
loadInQueue def@(Def _ id _ _ _) = do
  m <- get
  put $ M.insert (pretty id) def m
  Ex.return()
loadInQueue adt@(ADT _ _ _ _) = do
  Ex.return ()

-- noFileAtPath :: FilePath -> REPLStateIO ()
-- noFileAtPath pt = do
--     return $ Ex.throwError (FilePathError pt)
--
dumpStateAux ::M.Map String Def -> [String]
dumpStateAux m = do
  pDef (M.toList m)
  where
    pDef :: [(String, Def)] -> [String]
    pDef [] = []
    pDef ((k,v@(Def _ _ _ _ ty)):xs) = ((pretty k)++" : "++(pretty ty)) : pDef xs


handleCMD :: (?globals::Globals) => String -> REPLStateIO ()
handleCMD "" = Ex.return ()
handleCMD s =
   case (parseLine s) of
    Right l -> handleLine l
    Left msg -> do
       liftIO $ putStrLn msg

  where
    handleLine :: (?globals::Globals) => REPLExpr -> REPLStateIO ()
    handleLine DumpState = do
      dict <- get
      liftIO $ print $ dumpStateAux dict


    handleLine (LoadFile ptr) = do
      put M.empty
      ecs <- processFilesREPL ptr (let ?globals = ?globals in readToQueue)
      --liftIO $ print (concat ecs)
      return ()


helpMenu :: String
helpMenu =
      "-----------------------------------------------------------------------------------\n"++
      "                  The Granule Help Menu                                         \n"++
      "-----------------------------------------------------------------------------------\n"++
      ":help             (:h)  Display the help menu\n"++
      ":quit             (:q)  Quit Granule\n"++
      ":show <term>      (:s)  Display the Abstract Syntax Type of a term\n"++
      ":unfold <term>    (:u)  Unfold the expression into one without toplevel definition.\n"++
      ":dump             (:d)  Display the context\n"++
      ":load <filepath>  (:l)  Load an external file into the context\n"++
      "-----------------------------------------------------------------------------------"

{-  eer <- Ex.runExceptT (evalStateT (runInputT defaultSettings loop) M.empty)
  case eer of
    Right l -> return()
    Left er -> putStrLn $ show er -}

repl :: IO ()
repl = do
  eer <- Ex.runExceptT (evalStateT (runInputT defaultSettings loop) M.empty)
  case eer of
    Right l -> return ()
    Left er -> print er
   where
       loop :: InputT (StateT (M.Map String Def) (Ex.ExceptT ReplError IO)) ()
       loop = do
           minput <- getInputLine "Granule> "
           case minput of
               Nothing -> return ()
               Just [] -> loop
               Just input | input == ":q" || input == ":quit"
                              -> liftIO $ putStrLn "Leaving Granule." >> return ()
                          | input == ":h" || input == ":help"
                              -> (liftIO $ putStrLn helpMenu) >> loop
                          | otherwise -> let ?globals = defaultGlobals
                                          in do _ <- lift $ (handleCMD $ input) `Ex.catchError` handleError
                                                loop
         where
           handleError err = liftIO'.putStrLn.show $ err
