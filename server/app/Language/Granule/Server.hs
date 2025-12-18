{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}

module Language.Granule.Server where

import Control.Concurrent.MVar (MVar, newMVar, readMVar, modifyMVar)
import Control.Exception (try, SomeException)
import Control.Lens (to, (^.))
import Control.Monad.IO.Class
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Trans.Class
import Data.Default (Default(..))
import Data.Foldable (toList)
import Data.List (isInfixOf,isPrefixOf)
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
import Language.LSP.Protocol.Types
import Language.LSP.Protocol.Message
import Language.LSP.VFS
import qualified Language.LSP.Protocol.Lens as L

import Language.Granule.Checker.Monad
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Utils
import qualified Language.Granule.Checker.Checker as Checker
import qualified Language.Granule.Interpreter as Interpreter
import qualified Language.Granule.Syntax.Parser as Parser

type TextDocumentVersion = Int32 |? Null

data LsState = LsState { currentDefns :: M.Map String (Def () ()),
                         currentADTs :: M.Map String DataDecl }

instance Default LsState where
  def = LsState { currentDefns = M.empty,
                  currentADTs = M.empty }

newLsStateVar :: IO (MVar LsState)
newLsStateVar = newMVar def

type LspS = LspT () (ReaderT (MVar LsState) IO)

getLsState :: LspS LsState
getLsState = do
  state <- lift ask
  liftIO $ readMVar state

getDefns :: LspS (M.Map String (Def () ()))
getDefns = currentDefns <$> getLsState

getADTs :: LspS (M.Map String DataDecl)
getADTs = currentADTs <$> getLsState

putDefns :: M.Map String (Def () ()) -> LspS ()
putDefns d = modifyLsState $ \s -> s { currentDefns = d }

putADTs :: M.Map String DataDecl -> LspS ()
putADTs d = modifyLsState $ \s -> s { currentADTs = d }

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
  modifyLsState (\x -> def)
  flushDiagnosticsBySource 0 (Just "grls")
  pf <- lift $ lift $ serverParseFreshen (T.unpack content)
  case pf of
    Right (ast, extensions) -> let ?globals = ?globals {globalsExtensions = extensions} in do
      -- debugS $ T.pack (show ast)
      let (AST _ defns _ _ _) = ast
          defnIds = map (\x -> (pretty $ defId x, x)) defns
      putDefns (M.fromList defnIds)
      checked <- lift $ lift $ Checker.check ast
      case checked of
          Right _ -> do
            let (AST dd _ _ _ _) = ast
                declIds = map (\x -> (pretty $ dataDeclId x, x)) dd
            putADTs (M.fromList declIds)
          Left errs -> checkerDiagnostics doc version errs
    Left e ->
      if "Premature" `isPrefixOf` e
        then return ()
        else parserDiagnostic doc version e

parserDiagnostic :: NormalizedUri -> TextDocumentVersion -> String -> LspS ()
parserDiagnostic doc version message = do
  let diags =
        [ Diagnostic
            (getParseErrorRange message)
            (Just DiagnosticSeverity_Error)
            Nothing
            Nothing
            (Just "grls")
            (T.pack $ message ++ "\n")
            Nothing
            Nothing
            Nothing
        ]
  publishDiagnostics 1 doc (nullToMaybe version) (partitionBySource diags)

checkerDiagnostics :: (?globals :: Globals) => NormalizedUri -> TextDocumentVersion -> NonEmpty CheckerError -> LspS ()
checkerDiagnostics doc version l = do
  let diags = toList $ checkerErrorToDiagnostic doc version <$> l
  publishDiagnostics (Prelude.length diags) doc (nullToMaybe version) (partitionBySource diags)

checkerErrorToDiagnostic :: (?globals :: Globals) => NormalizedUri -> TextDocumentVersion -> CheckerError -> Diagnostic
checkerErrorToDiagnostic doc version e =
  let span = errLoc e
      (startLine, startCol) = let (x,y) = startPos span in (fromIntegral x, fromIntegral y)
      (endLine, endCol) = let (x,y) = endPos span in (fromIntegral x, fromIntegral y)
      message = title e ++ ":\n" ++ msg e
      in Diagnostic
          (Range (Position (startLine-1) (startCol-1)) (Position (endLine-1) endCol))
          (Just DiagnosticSeverity_Error)
          Nothing
          Nothing
          (Just "grls")
          (T.pack $ message ++ "\n")
          Nothing
          Nothing
          Nothing

objectToSymbol :: (?globals :: Globals) => (a -> Span) -> (a -> Id) -> a -> SymbolInformation
objectToSymbol objSpan objId obj = let loc = objSpan obj in SymbolInformation
  (T.pack $ pretty $ objId obj)
  SymbolKind_Variable
  (Nothing)
  (Nothing)
  (Nothing)
  (Location
      (filePathToUri $ filename loc)
      (Range
        (let (x, y) = startPos loc in Position (fromIntegral x-1) (fromIntegral y-1))
        (let (x, y) = endPos loc in Position (fromIntegral x-1) (fromIntegral y-1))))

posInSpan :: Position -> Span -> Bool
posInSpan (Position l c) s = let
  (testLine, testColumn) = (l+1, c+1)
  (startLine, startColumn) = let (x,y) = startPos s in (fromIntegral x, fromIntegral y)
  (endLine, endColumn) = let (x,y) = endPos s in (fromIntegral x, fromIntegral y)
  in (startLine < testLine && testLine < endLine) || (startLine == testLine && startColumn <= testColumn) || (testLine == endLine && testColumn <= endColumn)

spanToLocation :: Span -> Location
spanToLocation s = Location
    (filePathToUri $ filename s)
    (Range
      (let (x, y) = startPos s in Position (fromIntegral x-1) (fromIntegral y-1))
      (let (x, y) = endPos s in Position (fromIntegral x-1) (fromIntegral y-1)))

getWordAtPosition :: T.Text -> Position -> Maybe String
getWordAtPosition t (Position l c) = let ls = lines (T.unpack t) in
  if Prelude.length ls < fromIntegral l then Nothing else let
    targetLine = ls!!(fromIntegral l) in
      if Prelude.length targetLine < fromIntegral c then Nothing else
        Just $ getWordFromString targetLine (fromIntegral c) ""

getWordFromString :: String -> Int -> String -> String
getWordFromString [] _ acc = acc
getWordFromString (x:xs) 0 acc = if x == ' ' then acc else getWordFromString xs 0 (acc ++ [x])
getWordFromString (x:xs) n acc = if x == ' ' then getWordFromString xs (n-1) [] else getWordFromString xs (n-1) (acc ++ [x])

handlers :: (?globals :: Globals) => Handlers LspS
handlers = mconcat
  [ notificationHandler SMethod_Initialized $ \msg -> do
      return ()
  , notificationHandler SMethod_TextDocumentDidClose $ \msg -> do
      return ()
  , notificationHandler SMethod_CancelRequest $ \msg -> do
      return ()
  , notificationHandler SMethod_TextDocumentDidSave $ \msg -> do
      let doc = msg ^. L.params . L.textDocument . L.uri
          content = fromMaybe "?" $ msg ^. L.params . L.text
      validateGranuleCode (toNormalizedUri doc) (maybeToNull Nothing) content
  , notificationHandler SMethod_TextDocumentDidOpen $ \msg -> do
      let doc = msg ^. L.params . L.textDocument . L.uri
          content = msg ^. L.params . L.textDocument . L.text
      validateGranuleCode (toNormalizedUri doc) (maybeToNull Nothing) content
  , notificationHandler SMethod_TextDocumentDidChange $ \msg -> do
      let doc = msg ^. L.params . L.textDocument . L.uri . to toNormalizedUri
      mdoc <- getVirtualFile doc
      case mdoc of
        Just vf@(VirtualFile _ version _rope) -> do
          validateGranuleCode doc (maybeToNull (Just (fromIntegral version))) (virtualFileText vf)
        _ -> debugS $ "No virtual file found for: " <> (T.pack (show msg))
  , requestHandler SMethod_WorkspaceSymbol $ \req responder -> do
      let query = T.unpack $ req ^. L.params . L.query
      defns <- getDefns
      let possibleDefn = M.lookup query defns
      case possibleDefn of
        Nothing -> do
          decls <- getADTs
          let possibleDecl = M.lookup query decls
          case possibleDecl of
            Nothing -> do
              let constrs = concatMap (\x -> dataDeclDataConstrs x) decls
                  constrIds = M.fromList $ map (\x -> (pretty $ dataConstrId x, x)) constrs
                  possibleConstr = M.lookup query constrIds
              case possibleConstr of
                Nothing -> responder $ Right $ InR $ InR Null
                Just c -> responder $ Right $ InL [objectToSymbol dataConstrSpan dataConstrId c]
            Just d -> responder $ Right $ InL [objectToSymbol dataDeclSpan dataDeclId d]
        Just d -> responder $ Right $ InL [objectToSymbol defSpan defId d]
  , requestHandler SMethod_TextDocumentDefinition $ \req responder -> do
      let params = req ^. L.params
          pos = params ^. L.position
          doc = params ^. L.textDocument . L.uri . to toNormalizedUri
      mdoc <- getVirtualFile doc
      case mdoc of
        Just vf@(VirtualFile _ version _rope) -> do
          let t = virtualFileText vf
              query = getWordAtPosition t pos
          validateGranuleCode doc (maybeToNull (Just (fromIntegral version))) t
          case query of
            Nothing -> debugS $ "This should be impossible!"
            Just q -> do
              defns <- getDefns
              let possibleDefn = M.lookup q defns
              case possibleDefn of
                Nothing -> do
                  decls <- getADTs
                  let possibleDecl = M.lookup q decls
                  case possibleDecl of
                    Nothing -> do
                      let constrs = concatMap (\x -> dataDeclDataConstrs x) decls
                          constrIds = M.fromList $ map (\x -> (pretty $ dataConstrId x, x)) constrs
                          possibleConstr = M.lookup q constrIds
                      case possibleConstr of
                        Nothing -> responder $ Right $ InR $ InR Null
                        Just c -> responder $ Right $ InL $ Definition $ InL $ spanToLocation $ dataConstrSpan c
                    Just d -> responder $ Right $ InL $ Definition $ InL $ spanToLocation $ dataDeclSpan d
                Just d -> responder $ Right $ InL $ Definition $ InL $ spanToLocation $ defSpan d
        _ -> debugS $ "No virtual file found for: " <> (T.pack (show doc))
  ]

main :: IO Int
main = do
  globals <- Interpreter.getGrConfig >>= (return . Interpreter.grGlobals . snd)
  state <- newLsStateVar
  runServer $ ServerDefinition
    { onConfigChange = \_ -> pure ()
    , defaultConfig = ()
    , doInitialize = const . pure . Right
    , parseConfig = \_ _ -> Left "Not supported"
    , configSection = T.pack "granule"
    , staticHandlers = let ?globals = globals in (\_ -> handlers)
    , interpretHandler = \env -> Iso (\lsps -> runLspS lsps state env) liftIO
    , options =
      defaultOptions
        {
          optTextDocumentSync =
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
    syncKind = TextDocumentSyncKind_Full