{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
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
import Control.Exception (try)
import Control.Monad.State
import Control.Monad.Trans.Reader
import qualified Control.Monad.Except as Ex
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
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Interpreter.Eval
import qualified Language.Granule.Interpreter as Interpreter

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
  globals <- Interpreter.getGrConfig >>= (return . Interpreter.grGlobals . snd)

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
            liftIO (putStrLn "Leaving Granule.")

          | input == ":h" || input == ":help" ->
            liftIO (putStrLn helpMenu) >> loop st

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
   case parseLine s of
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
        Right ast -> liftIO $ print ast
        Left e -> do
          liftIO $ putStrLn "Input not an expression, checking for TypeScheme"
          pts <- liftIO' $ try $ either die return $ runReaderT (tscheme $ scanTokens str) "interactive"
          case pts of
            Right ts -> liftIO $ print ts
            Left err -> do
              st <- get
              Ex.throwError (ParseError err (files st))
              Ex.throwError (ParseError e (files st))

    handleLine (RunLexer str) = do
      liftIO $ print (scanTokens str)

    handleLine (ShowDef term) = do
      st <- get
      case M.lookup term (defns st) of
        Nothing -> Ex.throwError(TermNotInContext term)
        Just (def,_) -> liftIO $ print def

    handleLine (LoadFile ptr) = do
      -- Set up a clean slate
      modify (\st -> st { currentADTs = [], files = ptr, defns = M.empty })
      processFilesREPL ptr readToQueue
      return ()

    handleLine (Debuger ptr) = do
      let ?globals = ?globals {globalsDebugging = Just True } in handleLine (LoadFile ptr)

    handleLine (AddModule paths) = do
      -- Update paths to try the include path in case they do not exist locally
      paths <- liftIO' $ forM paths (\path -> do
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

    handleLine (CheckType exprString) = do
      expr <- parseExpression exprString
      ty <- synthTypeFromInputExpr expr
      let exprString' = if elem ' ' exprString && head exprString /= '(' && last exprString /= ')' then "(" <> exprString <> ")" else exprString
      liftIO $ putStrLn $ exprString' <> " : " <> either pretty pretty ty

    handleLine (Eval exprString) = do
      expr <- parseExpression exprString
      ty <- synthTypeFromInputExpr expr
      case ty of
        -- Well-typed, with `tyScheme`
        Left tyScheme -> do
          st <- get
          let ndef = buildDef (freeVarCounter st) tyScheme expr
          -- Update the free var counter
          modify (\st -> st { freeVarCounter = freeVarCounter st + 1 })

          let fv = freeVars expr
          let ast = buildForEval fv (defns st)
          let astNew = AST (currentADTs st) (ast <> [ndef]) mempty mempty Nothing
          result <- liftIO' $ try $ replEval (freeVarCounter st) astNew
          case result of
              Left e -> Ex.throwError (EvalError e)
              Right Nothing -> liftIO $ print "if here fix"
              Right (Just result) -> liftIO $ putStrLn $ pretty result
        -- If this was actually just a type, return it as is
        Right kind -> liftIO $ putStrLn exprString

parseExpression :: (?globals::Globals) => String -> REPLStateIO (Expr () ())
parseExpression exprString = do
  -- Check that the expression is well-typed first
  case runReaderT (expr $ scanTokens exprString) "interactive" of
    -- Not a syntactically well-formed term
    Left err -> Ex.throwError (ParseError' err)
    Right exprAst -> return exprAst

synthTypeFromInputExpr :: (?globals::Globals) => Expr () () -> REPLStateIO (Either TypeScheme Kind)
synthTypeFromInputExpr exprAst = do
  st <- get
  -- Build the AST and then try to synth the type
  let defs = map fst (M.elems (defns st))
  checkerResult <- liftIO' $ synthExprInIsolation (AST (currentADTs st) defs mempty mempty Nothing) exprAst
  case checkerResult of
    Right res -> return res
    Left err -> Ex.throwError (TypeCheckerError err)

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
replEval val (AST dataDecls defs _ _ _) = do
    bindings <- evalDefs builtIns (map toRuntimeRep defs)
    case lookup (mkId (" repl" <> show val)) bindings of
      Nothing -> return Nothing
      Just (Pure _ e)    -> fmap Just (evalIn bindings e)
      Just (Promote _ e) -> fmap Just (evalIn bindings e)
      Just val           -> return $ Just val

liftIO' :: IO a -> REPLStateIO a
liftIO' = lift.lift

processFilesREPL :: [FilePath] -> (FilePath -> REPLStateIO a) -> REPLStateIO [[a]]
processFilesREPL globPatterns f = forM globPatterns (\p -> do
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
                  let (AST dd def _ _ _) = ast
                  forM_ def $ \idef -> loadInQueue idef
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
    else put $ st { defns = M.insert (pretty id) (def, nub $ extractFreeVars id (freeVars def)) (defns st) }

dumpStateAux :: (?globals::Globals) => M.Map String (Def () (), [String]) -> [String]
dumpStateAux m = pDef (M.toList m)
  where
    pDef :: [(String, (Def () (), [String]))] -> [String]
    pDef [] = []
    pDef ((k,(v@(Def _ _ _ ty),dl)):xs) =  (pretty k <> " : " <> pretty ty) : pDef xs

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
        ids -> buildDef ids <> [def]
                  where
                    buildDef :: [String] -> [Def () ()]
                    buildDef [] =  []
                    buildDef (x:xs) =  buildDef xs <> buildAST x m

buildForEval :: [Id] -> M.Map String (Def () (), [String]) -> [Def () ()]
buildForEval [] _ = []
buildForEval (x:xs) m = buildAST (sourceName x) m <> buildForEval xs m

buildCheckerState :: (?globals::Globals) => [DataDecl] -> Checker.Checker ()
buildCheckerState dataDecls = do
    _ <- Checker.runAll checkTyCon dataDecls
    _ <- Checker.runAll checkDataCons dataDecls
    return ()

buildDef ::Int -> TypeScheme -> Expr () () -> Def () ()
buildDef rfv ts ex = Def nullSpanInteractive (mkId (" repl" <> show rfv))
   [Equation nullSpanInteractive () [] ex] ts