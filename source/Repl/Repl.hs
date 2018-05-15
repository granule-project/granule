{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PackageImports #-}
module Repl.Repl where

import System.FilePath
import System.FilePath.Find
import System.Directory
import qualified Data.Map as M
import qualified Checker.Monad as Mo
import qualified Data.ConfigFile as C
import Control.Exception (try)
import Control.Monad.State
import Control.Monad.Trans.Maybe
import System.Console.Haskeline
import System.Console.Haskeline.MonadException()
import Repl.ReplError
import "Glob" System.FilePath.Glob (glob, compile, globDir1)
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
import Control.Monad.Error

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

-- FileName to search for -> each path from repl path to search -> all found instances of file
rFind :: String -> FilePath -> IO [FilePath]
rFind fn fp = find always (fileName ==? fn) fp
-- name of file to find -> Repl File Paths -> should be a matching file path
rFindHelper :: String -> [FilePath] -> IO [FilePath]
rFindHelper fn [] = return []
rFindHelper fn (r:rfp) = do
  y <- rFind fn r
  x <-  rFindHelper fn rfp
  return (y ++ x)

rFindMain :: [String] -> [FilePath] -> IO [[FilePath]]
rFindMain fn rfp = forM fn $ (\x -> rFindHelper x rfp )

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


getConfigFile :: IO String
getConfigFile = do
  hd <- getHomeDirectory           -- .granule.conf
  let confile = hd ++ (pathSeparator:".granule.conf")
  dfe <- doesFileExist confile
  if dfe
    then return confile
    else return ""



-- replPathParse :: IO [FilePath]
-- replPathParse = do
--   pf <- getPathFile
--   case pf of
--     "" -> return []
--     _ -> do
--       let x = parsePath pf
--       case x of
--         Right l -> return l
--         Left msg -> return []





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

    handleLine (RunParser str) = do
      pexp <- liftIO' $ try $ expr $ scanTokens str
      case pexp of
        Right ast -> liftIO $ putStrLn (show ast)
        Left e -> do
          Ex.throwError (ParseError e)

    handleLine (RunLexer str) = do
      liftIO $ print $ show (scanTokens str)

    handleLine (ShowDef term) = do
      (_,_,_,_,m) <- get
      let def' = (M.lookup term m)
      case def' of
        Nothing -> Ex.throwError(TermNotInContext term)
        Just (def,_) -> liftIO $ print (show def)

        -- tester <- liftIO' $ rFindHelper (head ptr) rp
        -- liftIO $ print (show $ makeUnique tester)
    handleLine (LoadFile ptr) = do
      (fvg,rp,_,_,_) <- get
      tester <- liftIO' $ rFindMain ptr rp
      let lfp = makeUnique $ (concat tester)
      case lfp of
        [] -> do
          put (fvg,rp,[],ptr,M.empty)
          ecs <- processFilesREPL ptr (let ?globals = ?globals in readToQueue)
          return ()
        _ -> do
          put (fvg,rp,[],lfp,M.empty)
          ecs <- processFilesREPL lfp (let ?globals = ?globals in readToQueue)
          return ()

    handleLine (AddModule ptr) = do
      (fvg,rp,adt,f,m) <- get
      tester <- liftIO' $ rFindMain ptr rp
      let lfp = makeUnique $ (concat tester)
      case lfp of
        [] -> do
          put (fvg,rp,adt,(f++ptr),m)
          ecs <- processFilesREPL ptr (let ?globals = ?globals in readToQueue)
          return ()
        _ -> do
          put (fvg,rp,adt,(f++lfp),m)
          ecs <- processFilesREPL lfp (let ?globals = ?globals in readToQueue)
          return ()

    handleLine Reload = do
      (fvg,rp,adt,f,_) <- get
      put (fvg,rp,adt,f, M.empty)
      case f of
        [] -> liftIO $ putStrLn "No files to reload" >> return ()
        _ -> do
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
      ":show <term>       (:s)  Display AST of term in state\n"++
      ":parse <string>    (:p)  Run Granule parser on given string\n"++
      ":lexer <string>    (:x)  Run Granule lexer on given string and display [Token]\n"++
      ":dump              (:d)  Display the context\n"++
      ":load <filepath>   (:l)  Load an external file into the context\n"++
      ":module <filepath> (:m)  Add file/module to the current context\n"++
      "-----------------------------------------------------------------------------------"
-- ":unfold <term>     (:u)  Unfold the expression into one without toplevel definition.\n"++
-- ":show <term>       (:s)  Display the Abstract Syntax Type of a term\n"++

configFileStuff :: IO String
configFileStuff = do
  rt <- runErrorT $
    do
    cf <- liftIO $ getConfigFile
    case cf of
      "" ->  do
        lift $ putStrLn "ALERT : No config file found or loaded\nenter ':h' or ':help' for menu"
        return ""
      _ -> do
         cp <- liftIO $ C.readfile C.emptyCP cf --error is occuring at this step
         case cp of
           Right l -> do
             pths <- C.get l "DEFAULT" "PATH"
             return pths
  case rt of
    Right conpth -> return $ conpth
    Left conptherr -> do
      print conptherr
      return $ show conptherr

repl :: IO ()
repl = do
  someP <- configFileStuff
  let drp = (lines someP)
  runInputT defaultSettings (loop (0,drp,[],[],M.empty))
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
