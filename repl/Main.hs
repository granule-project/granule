{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PackageImports #-}
module Main where

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
import "Glob" System.FilePath.Glob (glob)
import Utils
import Syntax.Pretty
import Syntax.Expr
import Syntax.Parser
import Syntax.Lexer
import Checker.Checker
import Eval
import Context
--import qualified Checker.Primitives as Primitives
import qualified Control.Monad.Except as Ex

import ReplError
import ReplParser

type ReplPATH = [FilePath]
type ADT = [DataDecl]
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

replEval :: (?globals :: Globals) =>Int -> AST -> IO (Maybe Value)
replEval val (AST dataDecls defs) = do
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
            debugM "AST" (show ast)
            debugM "Pretty-printed AST:" $ pretty ast
            checked <-  liftIO' $ check ast
            case checked of
                Ok -> do
                    let (AST dd def) = ast
                    forM def $ \idef -> loadInQueue idef
                    (fvg,rp,adt,f,m) <- get
                    put (fvg,rp,(dd++adt),f,m)
                    liftIO $ putStrLn $ pth++", interpreted"
                Failed -> Ex.throwError (TypeCheckError pth)
      Left e -> Ex.throwError (ParseError e)



loadInQueue :: (?globals::Globals) => Def -> REPLStateIO  ()
loadInQueue def@(Def _ id exp _ _) = do
  (fvg,rp,adt,f,m) <- get
  if M.member (pretty id) m
  then Ex.throwError (TermInContext (pretty id))
  else put $ (fvg,rp,adt,f,M.insert (pretty id) (def,(makeUnique $ extractFreeVars id (freeVars def))) m)


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

startBuildADT :: [DataDecl] -> [DataConstr]
startBuildADT [] = []
startBuildADT ((DataDecl _ _ _ _ dc):dataDec) = dc ++ (startBuildADT dataDec)

makeMapBuildADT :: [DataConstr] -> M.Map String DataConstr
makeMapBuildADT adc = M.fromList $ tempADT adc
                        where
                          tempADT :: [DataConstr] -> [(String,DataConstr)]
                          tempADT [] = []
                          tempADT (dc@(DataConstrG _ id _):dct) = ((sourceName id),dc) : tempADT dct
                          tempADT (dc@(DataConstrA _ _ _):dct) = tempADT dct

lookupBuildADT :: (?globals::Globals) => String -> M.Map String DataConstr -> String
lookupBuildADT term aMap = let lup = M.lookup term aMap in
                            case lup of
                              Nothing -> ""
                              Just d -> pretty d

printType :: (?globals::Globals) => String -> M.Map String (Def, [String]) -> String
printType trm m = let v = M.lookup trm m in
                    case v of
                      Nothing ->""
                      Just (def@(Def _ id _ _ ty),lid) -> (pretty id)++" : "++(pretty ty)

buildForEval :: [Id] -> M.Map String (Def, [String]) -> [Def]
buildForEval [] _ = []
buildForEval (x:xs) m = buildAST (sourceName x) m ++ buildForEval xs m

synType :: (?globals::Globals) => Expr -> Ctxt TypeScheme -> Mo.CheckerState -> IO (Maybe (Type, Ctxt Mo.Assumption))
synType exp [] cs = liftIO $ Mo.evalChecker cs $ runMaybeT $ synthExpr empty empty Positive exp
synType exp cts cs = liftIO $ Mo.evalChecker cs $ runMaybeT $ synthExpr cts empty Positive exp

synTypeBuilder :: (?globals::Globals) => Expr -> [Def] -> [DataDecl] -> REPLStateIO Type
synTypeBuilder exp ast adt = do
  let ddts = buildCtxtTSDD adt
  (_,cs) <- liftIO $ Mo.runChecker Mo.initState $ buildCheckerState adt
  ty <- liftIO $ synType exp ((buildCtxtTS ast) ++ ddts) cs
  --liftIO $ print $ show ty
  case ty of
    Just (t,a) -> return t
    Nothing -> Ex.throwError OtherError'


buildCheckerState :: (?globals::Globals) => [DataDecl] -> Mo.Checker ()
buildCheckerState dd = do
    let checkDataDecls = do { mapM checkTyCon dd; mapM checkDataCons dd }
    somethine <- checkDataDecls
    return ()

buildCtxtTS :: (?globals::Globals) => [Def] -> Ctxt TypeScheme
buildCtxtTS [] = []
buildCtxtTS ((x@(Def _ id _ _ ts)):ast) =  (id,ts) : buildCtxtTS ast

buildCtxtTSDD :: (?globals::Globals) => [DataDecl] -> Ctxt TypeScheme
buildCtxtTSDD [] = []
buildCtxtTSDD ((DataDecl _ _ _ _ dc) : dd) = makeCtxt dc ++ buildCtxtTSDD dd
                                              where
                                                makeCtxt :: [DataConstr] -> Ctxt TypeScheme
                                                makeCtxt [] = []
                                                makeCtxt datcon = buildCtxtTSDDhelper datcon

buildCtxtTSDDhelper :: [DataConstr] -> Ctxt TypeScheme
buildCtxtTSDDhelper [] = []
buildCtxtTSDDhelper (dc@(DataConstrG _ id ts):dct) = (id,ts) : buildCtxtTSDDhelper dct
buildCtxtTSDDhelper (dc@(DataConstrA _ _ _):dct) = buildCtxtTSDDhelper dct


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
          liftIO $ putStrLn "Input not an expression, checking for TypeScheme"
          pts <- liftIO' $ try $ tscheme $ scanTokens str
          liftIO $ print $ scanTokens str
          case pts of
            Right ts -> liftIO $ putStrLn (show ts)
            Left err -> do
              Ex.throwError (ParseError err)
              Ex.throwError (ParseError e)


    handleLine (RunLexer str) = do
      liftIO $ putStrLn $ show (scanTokens str)

    handleLine (ShowDef term) = do
      (_,_,_,_,m) <- get
      let def' = (M.lookup term m)
      case def' of
        Nothing -> Ex.throwError(TermNotInContext term)
        Just (def,_) -> liftIO $ putStrLn (show def)

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


    handleLine (Debuger ptr) = do
      (fvg,rp,_,_,_) <- get
      tester <- liftIO' $ rFindMain ptr rp
      let lfp = makeUnique $ (concat tester)
      case lfp of
        [] -> do
          put (fvg,rp,[],ptr,M.empty)
          ecs <- processFilesREPL ptr (let ?globals = ?globals {debugging = True } in readToQueue)
          return ()
        _ -> do
          put (fvg,rp,[],lfp,M.empty)
          ecs <- processFilesREPL lfp (let ?globals = ?globals {debugging = True } in readToQueue)
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
        []  -> do
          let xtx = lookupBuildADT trm (makeMapBuildADT (startBuildADT adt))
          case xtx of
            "" -> Ex.throwError (TermNotInContext trm)
            _ -> liftIO $ putStrLn xtx
        ast -> do
          checked <- liftIO' $ check (AST adt ast)
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
                        typ <- liftIO $ synType exp [] Mo.initState
                        case typ of
                            Just (t,a) -> return ()
                            Nothing -> Ex.throwError (TypeCheckError ev)
                        result <- liftIO' $ try $ evalIn builtIns exp
                        case result of
                            Right r -> liftIO $ putStrLn (pretty r)
                            Left e -> Ex.throwError (EvalError e)
                    _ -> do
                        let ast = buildForEval fv m
                        typer <- synTypeBuilder exp ast adt
                        let ndef = buildDef fvg (buildTypeScheme typer) exp
                        put ((fvg+1),rp,adt,fp,m)
                        checked <- liftIO' $ check (AST adt (ast++(ndef:[])))
                        case checked of
                            Ok -> do
                                result <- liftIO' $ try $ replEval fvg (AST adt (ast++(ndef:[])))
                                case result of
                                    Left e -> Ex.throwError (EvalError e)
                                    Right Nothing -> liftIO $ print "if here fix"
                                    Right (Just result) -> liftIO $ putStrLn (pretty result)
                            Failed -> Ex.throwError (OtherError')
            Left e -> Ex.throwError (ParseError e) --error from parsing (pexp)

helpMenu :: String
helpMenu = unlines
      ["-----------------------------------------------------------------------------------"
      ,"                  The Granule Help Menu                                         "
      ,"-----------------------------------------------------------------------------------"
      ,":help                     (:h)  Display the help menu"
      ,":quit                     (:q)  Quit Granule"
      ,":type <term>              (:t)  Display the type of a term in the context"
      ,":show <term>              (:s)  Display Def of term in state"
      ,":parse <expression/type>  (:p)  Run Granule parser on a given expression and display Expr."
      ,"                                If input is not an expression will try to run against TypeScheme parser and display TypeScheme"
      ,":lexer <string>           (:x)  Run Granule lexer on given string and display [Token]"
      ,":debug <filepath>         (:d)  Run Granule debugger and display output while loading a file"
      ,":dump                     ()    Display the context"
      ,":load <filepath>          (:l)  Load an external file into the context"
      ,":module <filepath>        (:m)  Add file/module to the current context"
      ,":reload                   (:r)  Reload last file loaded into REPL"
      ,"-----------------------------------------------------------------------------------"
      ]

configFileGetPath :: IO String
configFileGetPath = do
  rt <- Ex.runExceptT $
    do
    cf <- liftIO $ getConfigFile
    case cf of
      "" ->  do
        lift $ putStrLn "ALERT: No config file found or loaded.\nPlease refer to README for config file creation and format\nEnter ':h' or ':help' for menu"
        return ""
      _ -> do
         cp <- liftIO $ C.readfile C.emptyCP cf
         case cp of
           Right l -> do
             pths <- C.get l "DEFAULT" "path"
             return pths
           Left r -> return ""
  case rt of
    Right conpth -> return $ conpth
    Left conptherr -> do
      liftIO $ putStrLn $ "ALERT: Path variable missing from config file.  Please refer to README for config file creation and formant"
      return ""

main :: IO ()
main = do
  someP <- configFileGetPath
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
