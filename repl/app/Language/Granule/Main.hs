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

import System.Exit (die)
import System.FilePath
import System.Directory

import Data.List (nub)

import qualified Data.Map as M
import qualified Language.Granule.Checker.Monad as Checker
import Data.List.NonEmpty (NonEmpty)
import Control.Exception (try)
import Control.Monad.State
import Control.Monad.Trans.Reader
import System.Console.Haskeline
import System.Console.Haskeline.MonadException()

import "Glob" System.FilePath.Glob (glob)
import Language.Granule.Utils
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Parser
import Language.Granule.Syntax.Lexer
import Language.Granule.Syntax.Span
import Language.Granule.Checker.Checker
import Language.Granule.Checker.Substitution
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Interpreter.Eval
import qualified Language.Granule.Interpreter as Interpreter
import Language.Granule.Context
--import qualified Language.Granule.Checker.Primitives as Primitives
import qualified Control.Monad.Except as Ex

import Language.Granule.ReplError
import Language.Granule.ReplParser

import Data.Version (showVersion)
import Paths_granule_repl (version)

-- Types used in the REPL
type ADT = [DataDecl]

type FreeVarGen = Int

data ReplState =
  ReplState
    { freeVarCounter :: FreeVarGen
    , currentADTs :: ADT
    , files :: [FilePath]
    , defns  :: M.Map String (Def () (), [String])
    }

initialState :: ReplState
initialState = ReplState 0 [] [] M.empty

type REPLStateIO a  = StateT ReplState (Ex.ExceptT ReplError IO) a

-- A span used for top-level inputs
nullSpanInteractive = Span (0,0) (0,0) "interactive"

main :: IO ()
main = do
  -- Welcome message
  putStrLn $ "\ESC[34;1mWelcome to Granule interactive mode (grepl). Version " <> showVersion version <> "\ESC[0m"

  -- Get the .granue config
  globals <- getGrConfigGlobals

  -- Run the REPL loop
  runInputT defaultSettings (let ?globals = globals in loop initialState)
   where
    loop :: (?globals :: Globals) => ReplState -> InputT IO ()
    loop st = do
      minput <- getInputLine "Granule> "
      case minput of
        Nothing -> return ()
        Just [] -> loop st
        Just input
          | input == ":q" || input == ":quit" ->
            liftIO $ putStrLn "Leaving Granule."

          | input == ":h" || input == ":help" ->
            (liftIO $ putStrLn helpMenu) >> loop st

          | otherwise -> do

            r <- liftIO $ Ex.runExceptT (runStateT (handleCMD input) st)
            case r of
              Right (_, st') -> loop st'
              Left err -> do
                liftIO $ print err
                -- And leave a space
                liftIO $ putStrLn ""
                case remembersFiles err of
                  Just fs -> loop (st { files = fs })
                  Nothing -> loop st

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

handleCMD :: (?globals::Globals) => String -> REPLStateIO ()
handleCMD "" = Ex.return ()
handleCMD s =
   case (parseLine s) of
    Right l -> handleLine l
    Left msg -> liftIO $ putStrLn msg

  where
    handleLine :: (?globals::Globals) => REPLExpr -> REPLStateIO ()
    handleLine DumpState = do
      st <- get
      liftIO $ print $ dumpStateAux (defns st)

    handleLine (RunParser str) = do
      pexp <- liftIO' $ try $ either die return $ runReaderT (expr $ scanTokens str) "interactive"
      case pexp of
        Right ast -> liftIO $ putStrLn (show ast)
        Left e -> do
          liftIO $ putStrLn "Input not an expression, checking for TypeScheme"
          pts <- liftIO' $ try $ either die return $ runReaderT (tscheme $ scanTokens str) "interactive"
          case pts of
            Right ts -> liftIO $ putStrLn (show ts)
            Left err -> do
              st <- get
              Ex.throwError (ParseError err (files st))
              Ex.throwError (ParseError e (files st))


    handleLine (RunLexer str) = do
      liftIO $ putStrLn $ show (scanTokens str)

    handleLine (ShowDef term) = do
      st <- get
      case M.lookup term (defns st) of
        Nothing -> Ex.throwError(TermNotInContext term)
        Just (def,_) -> liftIO $ putStrLn (show def)

    handleLine (LoadFile ptr) = do
      -- Set up a clean slate
      modify (\st -> st { currentADTs = [], files = ptr, defns = M.empty })
      processFilesREPL ptr readToQueue
      return ()

    handleLine (Debuger ptr) = do
      let ?globals = ?globals {globalsDebugging = Just True } in handleLine (LoadFile ptr)

    handleLine (AddModule paths) = do
      -- Update paths to try the include path in case they do not exist locally
      paths <- liftIO' $ forM paths $ (\path -> do
                localFile <- doesFileExist path
                return $ if localFile
                  then path
                  else case globalsIncludePath ?globals of
                          Just includePath -> includePath <> (pathSeparator : path)
                          Nothing          -> path)

      modify (\st -> st { files = files st <> paths })
      processFilesREPL paths readToQueue
      return ()

    handleLine Reload = do
      st <- get
      case files st of
        [] -> liftIO $ putStrLn "No files to reload"
        files -> do
          modify (\st -> st { currentADTs = [], defns = M.empty })
          processFilesREPL files readToQueue
          return ()

    handleLine (CheckType trm) = do
      st <- get
      case buildAST trm (defns st) of
        []  ->
          case lookupBuildADT trm (makeMapBuildADT (startBuildADT (currentADTs st))) of
            "" -> Ex.throwError (TermNotInContext trm)
            err -> liftIO $ putStrLn err
        ast -> do
          -- TODO: use the type that comes out of the checker to return the type
          checked <- liftIO' $ check (AST (currentADTs st) ast mempty)
          case checked of
            Right _ -> liftIO $ putStrLn (printType trm (defns st))
            Left err -> Ex.throwError (TypeCheckerError err)

    handleLine (Eval ev) = do
        pexp <- liftIO' $ try $ either die return $ runReaderT (expr $ scanTokens ev) "interactive"
        case pexp of
            Right exp -> do
              case freeVars exp of
                [] -> do -- simple expressions
                    typ <- liftIO $ synType exp [] Checker.initState
                    case typ of
                        Right (t, a, _) -> return ()
                        Left err -> Ex.throwError (TypeCheckerError err)

                    result <- liftIO' $ try $ evalIn builtIns (toRuntimeRep exp)
                    case result of
                        Right r -> liftIO $ putStrLn (pretty r)
                        Left e -> Ex.throwError (EvalError e)
                fv -> do
                    st <- get
                    let ast = buildForEval fv (defns st)
                    typer <- synTypeBuilder exp ast (currentADTs st)
                    let ndef = buildDef (freeVarCounter st) (buildTypeScheme typer) exp
                    -- Update the free var counter
                    modify (\st -> st { freeVarCounter = freeVarCounter st + 1 })
                    -- TODO: cons ndef to the front?
                    let astNew = AST (currentADTs st) (ast <> [ndef]) mempty
                    checked <- liftIO' $ check astNew
                    case checked of
                        Right _ -> do
                            result <- liftIO' $ try $ replEval (freeVarCounter st) astNew
                            case result of
                                Left e -> Ex.throwError (EvalError e)
                                Right Nothing -> liftIO $ print "if here fix"
                                Right (Just result) -> liftIO $ putStrLn (pretty result)
                        Left err -> Ex.throwError (TypeCheckerError err)
            Left e -> do
              st <- get
              Ex.throwError (ParseError e (files st)) --error from parsing (pexp)

getGrConfigGlobals :: IO Globals
getGrConfigGlobals = Interpreter.getGrConfig >>= (return . Interpreter.grGlobals . snd)


-- Exceptions behaviour
instance MonadException m => MonadException (StateT ReplState m) where
  controlIO f = StateT $ \s -> controlIO $ \(RunIO run) -> let
                  run' = RunIO (fmap (StateT . const) . run . flip runStateT s)
                  in fmap (flip runStateT s) $ f run'

instance MonadException m => MonadException (Ex.ExceptT e m) where
  controlIO f = Ex.ExceptT $ controlIO $ \(RunIO run) -> let
                  run' = RunIO (fmap Ex.ExceptT . run . Ex.runExceptT)
                  in fmap Ex.runExceptT $ f run'

replEval :: (?globals :: Globals) => Int -> AST () () -> IO (Maybe RValue)
replEval val (AST dataDecls defs _) = do
    bindings <- evalDefs builtIns (map toRuntimeRep defs)
    case lookup (mkId (" repl"<>(show val))) bindings of
      Nothing -> return Nothing
      Just (Pure _ e)    -> fmap Just (evalIn bindings e)
      Just (Promote _ e) -> fmap Just (evalIn bindings e)
      Just val           -> return $ Just val

liftIO' :: IO a -> REPLStateIO a
liftIO' = lift.lift

processFilesREPL :: [FilePath] -> (FilePath -> REPLStateIO a) -> REPLStateIO [[a]]
processFilesREPL globPatterns f = forM globPatterns $ (\p -> do
    filePaths <- liftIO $ glob p
    case filePaths of
      [] -> lift $ Ex.throwError (FilePathError p)
      _ -> forM filePaths f)

readToQueue :: (?globals::Globals) => FilePath -> REPLStateIO ()
readToQueue path = let ?globals = ?globals{ globalsSourceFilePath = Just path } in do
    pf <- liftIO' $ try $ parseAndDoImportsAndFreshenDefs =<< readFile path

    case pf of
      Right ast -> do
            debugM "AST" (show ast)
            debugM "Pretty-printed AST:" $ pretty ast
            checked <- liftIO' $ check ast
            case checked of
                Right _ -> do
                  let (AST dd def _) = ast
                  forM def $ \idef -> loadInQueue idef
                  modify (\st -> st { currentADTs = dd <> currentADTs st })
                  liftIO $ printInfo $ green $ path <> ", interpreted."

                Left errs -> do
                  Ex.throwError (TypeCheckerError errs)
      Left e -> do
       st <- get
       Ex.throwError (ParseError e (files st))

loadInQueue :: (?globals::Globals) => Def () () -> REPLStateIO  ()
loadInQueue def@(Def _ id _ _) = do
  st <- get
  if M.member (pretty id) (defns st)
    then Ex.throwError (TermInContext (pretty id))
    else put $ st { defns = M.insert (pretty id) (def,(nub $ extractFreeVars id (freeVars def))) (defns st) }

dumpStateAux :: (?globals::Globals) => M.Map String (Def () (), [String]) -> [String]
dumpStateAux m = pDef (M.toList m)
  where
    pDef :: [(String, (Def () (), [String]))] -> [String]
    pDef [] = []
    pDef ((k,(v@(Def _ _ _ ty),dl)):xs) = ((pretty k)<>" : "<>(pretty ty)) : pDef xs

extractFreeVars :: Id -> [Id] -> [String]
extractFreeVars _ []     = []
extractFreeVars i (x:xs) =
  if sourceName x == internalName x && sourceName x /= sourceName i
    then sourceName x : extractFreeVars i xs
    else extractFreeVars i xs

buildAST ::String -> M.Map String (Def () (), [String]) -> [Def () ()]
buildAST t m =
  case M.lookup t m  of
    Nothing ->
      -- Check primitives
      case lookup (mkId t) Primitives.builtins of
        Nothing -> []
        -- Create a trivial definition (x = x) with the right type
        Just ty -> [Def nullSpanInteractive (mkId t) [] ty]
        --   (Val nullSpanInteractive () (Var () (mkId t)))
    Just (def,lid) ->
      case lid of
        []  ->  [def]
        ids -> (buildDef ids <> [def])
                  where
                    buildDef :: [String] -> [Def () ()]
                    buildDef [] =  []
                    buildDef (x:xs) =  buildDef xs<>(buildAST x m)

startBuildADT :: [DataDecl] -> [DataConstr]
startBuildADT [] = []
startBuildADT ((DataDecl _ _ _ _ dc):dataDec) = dc <> (startBuildADT dataDec)

makeMapBuildADT :: [DataConstr] -> M.Map String DataConstr
makeMapBuildADT adc =
    M.fromList $ tempADT adc
  where
    tempADT :: [DataConstr] -> [(String,DataConstr)]
    tempADT [] = []
    tempADT (dc@(DataConstrIndexed _ id _):dct) = ((sourceName id),dc) : tempADT dct
    tempADT (dc@(DataConstrNonIndexed _ _ _):dct) = tempADT dct

lookupBuildADT :: (?globals::Globals) => String -> M.Map String DataConstr -> String
lookupBuildADT term aMap =
  case M.lookup term aMap of
    Nothing ->
      case lookup (mkId term) Primitives.typeConstructors of
        Nothing -> ""
        Just (k, _) -> term <> " : " <> pretty k
    Just d -> pretty d

printType :: (?globals::Globals) => String -> M.Map String (Def () (), [String]) -> String
printType trm m =
  case M.lookup trm m of
    Nothing ->
      case lookup (mkId trm) Primitives.builtins of
        Nothing -> "Unknown"
        Just ty -> trm <> " : " <> pretty ty
    Just (def@(Def _ id _ ty),lid) -> (pretty id)<>" : "<>(pretty ty)

buildForEval :: [Id] -> M.Map String (Def () (), [String]) -> [Def () ()]
buildForEval [] _ = []
buildForEval (x:xs) m = buildAST (sourceName x) m <> buildForEval xs m

synType :: (?globals::Globals)
  => Expr () ()
  -> Ctxt TypeScheme
  -> Checker.CheckerState
  -> IO (Either (NonEmpty Checker.CheckerError) (Type, Ctxt Checker.Assumption, Expr () Type))
synType exp cts cs = liftIO $ Checker.evalChecker cs $ do
  (ty, ctxt, subst, elab) <- synthExpr cts empty Positive exp
  ty <- substitute subst ty
  return (ty, ctxt, elab)

synTypeBuilder :: (?globals::Globals) => Expr () () -> [Def () ()] -> [DataDecl] -> REPLStateIO Type
synTypeBuilder exp ast adt = do
  let ddts = buildCtxtTSDD adt
  (_, cs) <- liftIO $ Checker.runChecker Checker.initState $ buildCheckerState adt
  ty <- liftIO $ synType exp ((buildCtxtTS ast) <> ddts) cs
  --liftIO $ print $ show ty
  case ty of
    Right (t, a, _) -> return t
    Left err -> Ex.throwError (TypeCheckerError err)


buildCheckerState :: (?globals::Globals) => [DataDecl] -> Checker.Checker ()
buildCheckerState dataDecls = do
    _ <- Checker.runAll checkTyCon dataDecls
    _ <- Checker.runAll checkDataCons dataDecls
    return ()

buildCtxtTS :: (?globals::Globals) => [Def () ()] -> Ctxt TypeScheme
buildCtxtTS [] = []
buildCtxtTS ((x@(Def _ id _ ts)):ast) =  (id,ts) : buildCtxtTS ast

buildCtxtTSDD :: (?globals::Globals) => [DataDecl] -> Ctxt TypeScheme
buildCtxtTSDD [] = []
buildCtxtTSDD ((DataDecl _ _ _ _ dc) : dd) =
    makeCtxt dc <> buildCtxtTSDD dd
  where
    makeCtxt :: [DataConstr] -> Ctxt TypeScheme
    makeCtxt [] = []
    makeCtxt datcon = buildCtxtTSDDhelper datcon

buildCtxtTSDDhelper :: [DataConstr] -> Ctxt TypeScheme
buildCtxtTSDDhelper [] = []
buildCtxtTSDDhelper (dc@(DataConstrIndexed _ id ts):dct) = (id,ts) : buildCtxtTSDDhelper dct
buildCtxtTSDDhelper (dc@(DataConstrNonIndexed _ _ _):dct) = buildCtxtTSDDhelper dct

buildTypeScheme :: (?globals::Globals) => Type -> TypeScheme
buildTypeScheme ty = Forall nullSpanInteractive [] [] ty

buildDef ::Int -> TypeScheme -> Expr () () -> Def () ()
buildDef rfv ts ex = Def nullSpanInteractive (mkId (" repl"<>(show rfv)))
   [Equation nullSpanInteractive () [] ex] ts