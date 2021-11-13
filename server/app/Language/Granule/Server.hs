{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Granule.Server where

import Control.Concurrent.MVar (MVar, newMVar, readMVar, putMVar, modifyMVar)
import Control.Exception (try, SomeException)
import Control.Lens (to, (^.))
import Control.Monad.IO.Class
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.State.Class (MonadState(..))
import Control.Monad.Trans.Class
import Data.Default (Default(..))
import Data.Foldable (toList)
import Data.List (isInfixOf)
import Data.List.NonEmpty (NonEmpty)
import Data.List.Split
import Data.Maybe (fromMaybe)
import Data.Set (Set, (\\), fromList, insert, empty)
import System.Directory (doesFileExist)
import System.FilePath ((</>), takeBaseName)
import System.IO (stderr)
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Language.LSP.Diagnostics
import Language.LSP.Server
import Language.LSP.Types
import Language.LSP.VFS
import qualified Language.LSP.Types.Lens as L

import Language.Granule.Checker.Monad
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span
import Language.Granule.Utils
import qualified Language.Granule.Checker.Checker as Checker
import qualified Language.Granule.Interpreter as Interpreter
import qualified Language.Granule.Syntax.Parser as Parser

data LsState = LsState { currentAst :: Maybe (AST () ()) }

instance Default LsState where 
  def = LsState { currentAst = Nothing }

newLsStateVar :: IO (MVar LsState)
newLsStateVar = newMVar def

type LspS = LspT () (ReaderT (MVar LsState) IO)

instance MonadState (Maybe (AST () ())) LspS where
  get = getAst
  put = putAst

getLsState :: LspS LsState
getLsState = do
  state <- lift ask
  liftIO $ readMVar state

getAst :: LspS (Maybe (AST () ()))
getAst = currentAst <$> getLsState

putLsState :: LsState -> LspS ()
putLsState s = do
  state <- lift ask
  liftIO $ putMVar state s

putAst :: Maybe (AST () ()) -> LspS ()
putAst a = modifyLsState $ \s -> s { currentAst = a }

modifyLsState :: (LsState -> LsState) -> LspS ()
modifyLsState m = do
  state <- lift ask
  liftIO $ modifyMVar state $ \s -> return (m s, ())

runLspS :: LspS a -> MVar LsState -> LanguageContextEnv () -> IO a
runLspS lsps state cfg = runReaderT (runLspT cfg lsps) state

fromUri :: NormalizedUri -> FilePath
fromUri = fromNormalizedFilePath . fromMaybe "<unknown>" . uriToNormalizedFilePath

debugS :: MonadIO m => T.Text -> m ()
debugS msg = liftIO $ T.hPutStrLn stderr $ "[grls] " <> msg

serverParseFreshen :: (?globals :: Globals) => String -> IO (Either String (AST () (), [Extension]))
serverParseFreshen input = do
  output <- try $ serverParse input
  case output of
    Right (Left s) -> return $ Left s
    Right (Right (ast, extensions)) -> return $ Right (freshenAST ast, extensions)
    Left (err :: SomeException) -> return $ Left $ show err

serverParse :: (?globals :: Globals) => String -> IO (Either String (AST () (), [Extension]))
serverParse input = do
    let output = Parser.parseDefs sourceFilePath input
    case output of
      Left s -> return $ Left s
      Right (ast, extensions) -> case moduleName ast of
        Nothing -> doImportsRecursively (imports ast) (ast { imports = empty }, extensions)
        Just (Id name _) ->
          if name == takeBaseName sourceFilePath
            then doImportsRecursively (imports ast) (ast { imports = empty }, extensions)
            else do
              return $ Left $ "Module name `" <> name <> "` does not match filename `" <> takeBaseName sourceFilePath <> "`"
  where
    doImportsRecursively :: Set Import -> (AST () (), [Extension]) -> IO (Either String (AST () (), [Extension]))
    doImportsRecursively todo (ast@(AST dds defs done hidden name), extensions) = do
      case toList (todo \\ done) of
        [] -> return $ Right (ast, extensions)
        (i:todo) -> do
          fileLocal <- doesFileExist i
          let path = if fileLocal then i else includePath </> i
          let ?globals = ?globals { globalsSourceFilePath = Just path } in do
            src <- readFile path
            output <- return $ Parser.parseDefs path src
            case output of
              Left s -> return $ Left s
              Right (AST dds' defs' imports' hidden' _, extensions') ->
                doImportsRecursively
                  (fromList todo <> imports')
                  (AST (dds' <> dds) (defs' <> defs) (insert i done) (hidden `M.union` hidden') name, extensions ++ extensions')

noRange :: Range
noRange = Range (Position 0 0) (Position 100000 0)

getParseErrorRange :: String -> Range
getParseErrorRange s = if isInfixOf "parse error" s then 
    let _:xs = splitOn ".gr:" s
        line:col:_ = numsFromString (concat xs)
        (l, c) = ((read line - 1), (read col - 1))
    in Range (Position l c) (Position l (c+1))
  else if isInfixOf "lexical error" s then
    let line:col:_ = numsFromString s
        (l, c) = ((read line - 1), (read col - 1))
    in Range (Position l c) (Position l (c+1))
  else noRange

numsFromString :: String -> [String]
numsFromString s = words $ map (\x -> if x `elem` ("0123456789" :: String) then x else ' ') s

validateGranuleCode :: (?globals :: Globals) => NormalizedUri -> TextDocumentVersion -> T.Text -> LspS ()
validateGranuleCode doc version content = let ?globals = ?globals {globalsSourceFilePath = Just $ fromUri doc} in do
  -- debugS $ "Validating: " <> T.pack (show doc) <> " ( " <> content <> ")"
  put Nothing
  flushDiagnosticsBySource 0 (Just "grls")
  pf <- lift $ lift $ serverParseFreshen (T.unpack content)
  case pf of
    Right (ast, extensions) -> let ?globals = ?globals {globalsExtensions = extensions} in do
      -- debugS $ T.pack (show ast)
      checked <- lift $ lift $ Checker.check ast
      case checked of
          Right _ -> do
            put (Just ast)
          Left errs -> checkerDiagnostics doc version errs
    Left e -> parserDiagnostic doc version e

parserDiagnostic :: NormalizedUri -> TextDocumentVersion -> String -> LspS ()
parserDiagnostic doc version message = do
  let diags = 
        [ Diagnostic
            (getParseErrorRange message)
            (Just DsError)
            Nothing
            (Just "grls")
            (T.pack $ message ++ "\n")
            Nothing
            (Just (List []))
        ]
  publishDiagnostics 1 doc version (partitionBySource diags)

checkerDiagnostics :: (?globals :: Globals) => NormalizedUri -> TextDocumentVersion -> NonEmpty CheckerError -> LspS ()
checkerDiagnostics doc version l = do
  let diags = toList $ checkerErrorToDiagnostic doc version <$> l
  publishDiagnostics (Prelude.length diags) doc version (partitionBySource diags)

checkerErrorToDiagnostic :: (?globals :: Globals) => NormalizedUri -> TextDocumentVersion -> CheckerError -> Diagnostic
checkerErrorToDiagnostic doc version e =
  let span = errLoc e
      (startLine, startCol) = startPos span
      (endLine, endCol) = endPos span
      message = title e ++ ":\n" ++ msg e
      in Diagnostic
          (Range (Position (startLine-1) (startCol-1)) (Position (endLine-1) (endCol+1)))
          (Just DsError)
          Nothing
          (Just "grls")
          (T.pack $ message ++ "\n")
          Nothing
          (Just (List []))

handlers :: (?globals :: Globals) => Handlers LspS
handlers = mconcat
  [ notificationHandler SInitialized $ \msg -> do
      return ()
  , notificationHandler STextDocumentDidClose $ \msg -> do
      return ()
  , notificationHandler STextDocumentDidSave $ \msg -> do
      let doc = msg ^. L.params . L.textDocument . L.uri
          content = fromMaybe "?" $ msg ^. L.params . L.text
      validateGranuleCode (toNormalizedUri doc) Nothing content
  , notificationHandler STextDocumentDidOpen $ \msg -> do
      let doc = msg ^. L.params . L.textDocument . L.uri
          content = msg ^. L.params . L.textDocument . L.text
      validateGranuleCode (toNormalizedUri doc) Nothing content
  , notificationHandler STextDocumentDidChange $ \msg -> do
      let doc = msg ^. L.params . L.textDocument . L.uri . to toNormalizedUri
      mdoc <- getVirtualFile doc
      case mdoc of
        Just vf@(VirtualFile _ version _rope) -> do
          validateGranuleCode doc (Just version) (virtualFileText vf)
        _ -> debugS $ "No virtual file found for: " <> (T.pack (show msg))
  ]

main :: IO Int
main = do
  globals <- Interpreter.getGrConfig >>= (return . Interpreter.grGlobals . snd)
  state <- newLsStateVar
  runServer $ ServerDefinition
    { onConfigurationChange = const $ const $ Right ()
    , defaultConfig = ()
    , doInitialize = const . pure . Right
    , staticHandlers = (let ?globals = globals in handlers)
    , interpretHandler = \env -> Iso (\lsps -> runLspS lsps state env) liftIO
    , options = 
      defaultOptions
        {
          textDocumentSync = 
            Just
              ( TextDocumentSyncOptions
                (Just True)
                (Just syncKind)
                (Just False)
                (Just False)
                (Just $ InR $ SaveOptions $ Just True)
              )
        }
    }
  where
    syncKind = TdSyncFull