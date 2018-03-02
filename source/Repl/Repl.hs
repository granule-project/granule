{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Repl.Repl where

import qualified Data.Map as M
import Control.Exception (SomeException, try)
import Control.Monad.State
import System.Console.Haskeline
-- import System.Console.Haskeline.MonadException
import System.Exit
import System.FilePath.Glob (glob)
import Utils
import Syntax.Pretty
import Syntax.Expr
import Syntax.Parser
import Repl.ReplParser
import Checker.Checker


type REPLStateIO = StateT (M.Map String Def) IO
instance MonadException m => MonadException (StateT (M.Map String Def) m) where
    controlIO f = StateT $ \s -> controlIO $ \(RunIO run) -> let
                    run' = RunIO (fmap (StateT . const) . run . flip runStateT s)
                    in fmap (flip runStateT s) $ f run'


io :: IO a -> REPLStateIO a
io i = liftIO i

-- prettyDef :: (QDefName, QDefDef) -> String
-- prettyDef elem = case getQDef elem of
--     (a, t@(Def _ _ _ _ ty)) -> (pretty a)++" : "++(show t)

processFilesREPL :: [FilePath] -> (FilePath -> REPLStateIO a) -> (FilePath -> REPLStateIO a) -> REPLStateIO [[a]]
processFilesREPL globPatterns e f = forM globPatterns $ (\p -> do
    filePaths <- io $ glob p
    case filePaths of
        [] -> (e p) >>= (return.(:[]))
        _ -> forM filePaths f)

readToQueue :: (?globals::Globals) => FilePath -> REPLStateIO ExitCode
readToQueue pth = do
    pf <- io $ try $ parseDefs =<< readFile pth
    case pf of
      Right (ast, maxFreshId) -> do
            let ?globals = ?globals { freshIdCounter = maxFreshId }
            checked <- io $ check ast
            case checked of
                Ok -> do
                    forM ast $ \idef -> loadInQueue idef
                    return ExitSuccess
                Failed -> return (ExitFailure 1)
      Left (e :: SomeException) -> do
            return $ print $ show e
            return (ExitFailure 1)
loadInQueue :: Def -> REPLStateIO ()
loadInQueue def@(Def _ id _ _ _) = do
  m <- get
  put $ M.insert (pretty id) def m
loadInQueue adt@(ADT _ _ _ _) = do
        return ()

noFileAtPath :: FilePath -> REPLStateIO ExitCode
noFileAtPath pt = do
    io $ print $ "The file path "++pt++" does not exist"
    return (ExitFailure 1)

dumpStateAux ::M.Map String Def -> [String]
dumpStateAux m = do
  pDef (M.toList m)
  where
    pDef :: [(String, Def)] -> [String]
    pDef [] = []
    pDef ((k,v@(Def _ _ _ _ ty)):xs) = ((pretty k)++" : "++(pretty ty)) : pDef xs



handleCMD :: (?globals::Globals) => String -> REPLStateIO ()
handleCMD "" = return ()
handleCMD s =
   case (parseLine s) of
    Right l -> handleLine l
    Left msg -> io $ putStrLn msg
  where
    handleLine :: (?globals::Globals) => REPLExpr -> REPLStateIO ()
    handleLine DumpState = do
      dict <- get
      io $ print $ dumpStateAux dict


    handleLine (LoadFile ptr) = do
      ecs <- processFilesREPL ptr noFileAtPath (let ?globals = ?globals in readToQueue)
      if all (== ExitSuccess) (concat ecs) then io.putStrLn $ "File(s) loaded" else io.putStrLn $ "Error while loading file(s)"


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

repl :: IO ()
repl = do
  evalStateT (runInputT defaultSettings loop) M.empty
   where
       loop :: InputT REPLStateIO ()
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
                                          in (lift.handleCMD $ input) >> loop
