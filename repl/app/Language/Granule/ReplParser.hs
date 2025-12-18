{-#
LANGUAGE
  NoMonomorphismRestriction,
  PackageImports,
  TemplateHaskell,
  FlexibleContexts
#-}
module Language.Granule.ReplParser where

import Prelude
import qualified Data.Text as T
import Text.Parsec
import qualified Text.Parsec.Token as Token
import Text.Parsec.Language
import Data.Functor.Identity


lexer :: GenLanguageDef String u Identity
lexer = haskellStyle {
    Token.reservedOpNames = [":", "let"]
}

type Parser a = ParsecT String () Identity a

tokenizer :: Token.GenTokenParser String u Identity
tokenizer = Token.makeTokenParser lexer

reservedOp :: String -> Parser ()
reservedOp = Token.reservedOp tokenizer

ws :: Parser ()
ws = Token.whiteSpace tokenizer

symbol :: String -> Parser String
symbol = Token.symbol tokenizer

data REPLExpr =
      ShowDef String
    | Holes
    | DumpState
    | LoadFile [FilePath]
    | AddModule [FilePath]
    | Reload
    | CheckType String
    | Eval String
    | RunParser String
    | RunLexer String
    | Debuger [FilePath]
    deriving Show

replTermCmdParser :: String -> String -> (t -> b) -> Parser t -> Parser b
replTermCmdParser short long c p = do
    _ <- symbol ":"
    cmd <- many lower
    ws
    t <- p
    eof
    if (cmd == long || cmd == short)
    then return $ c t
    else fail $ "Command \":"<>cmd<>"\" is unrecognized."

replIntCmdParser :: String -> String -> b -> Parser b
replIntCmdParser short long c = do
    _ <- symbol ":"
    cmd <- many lower
    eof
    if (cmd == long || cmd == short)
    then return c
    else fail $ "Command \":"<>cmd<>"\" is unrecognized."

replTyCmdParser :: String -> String -> (String -> b) -> Parser b
replTyCmdParser short long c = do
    _ <- symbol ":"
    cmd <- many lower
    ws
    term <- many1 anyChar
    eof
    if (cmd == long || cmd == short)
    then return $ c term
    else fail $ "Command \":"<>cmd<>"\" is unrecognized."

replTySchCmdParser :: String -> String -> (String -> b) -> Parser b
replTySchCmdParser short long c = do
    _ <- symbol ":"
    cmd <- many (lower <|> char '_')
    ws
    term <- many1 anyChar
    eof
    if (cmd == long || cmd == short)
    then return $ c term
    else fail $ "Command \":"<>cmd<>"\" is unrecognized."

replFileCmdParser :: String -> String -> ([FilePath] -> b) -> Parser b
replFileCmdParser short long c = do
    _ <- symbol ":"
    cmd <- many lower
    ws
    pathUntrimned <- many1 anyChar
    eof
    if(cmd == long || cmd == short)
    then do
        let tpath = T.words . T.pack $ pathUntrimned
        let fpath = textToFilePath tpath
        return $ c fpath
    else fail $ "Command \":"<>cmd<>"\" is unrecognized."

evalParser :: Parser REPLExpr
evalParser = do
  ev <- many anyChar
  return $ Eval ev
-- showASTParser = replTermCmdParser "s" "show" ShowAST

-- unfoldTermParser = replTermCmdParser "u" "unfold" Unfold

showHolesParser :: Parser REPLExpr
showHolesParser = replIntCmdParser "holes" "holes" Holes

dumpStateParser :: Parser REPLExpr
dumpStateParser = replIntCmdParser "dump" "dump" DumpState

loadFileParser :: Parser REPLExpr
loadFileParser = replFileCmdParser "l" "load" LoadFile

replDebugger :: Parser REPLExpr
replDebugger = replFileCmdParser "d" "debug" Debuger

addModuleParser :: Parser REPLExpr
addModuleParser = replFileCmdParser "m" "module" AddModule

reloadFileParser :: Parser REPLExpr
reloadFileParser = replIntCmdParser "r" "reload" Reload

checkTypeParser :: Parser REPLExpr
checkTypeParser = replTyCmdParser "t" "type" CheckType

showAstParser :: Parser REPLExpr
showAstParser = replTyCmdParser "s" "show" ShowDef

runParserRepl :: Parser REPLExpr
runParserRepl = replTyCmdParser "p" "parse" RunParser

runLexer :: Parser REPLExpr
runLexer = replTyCmdParser "x" "lexer" RunLexer

pathParser :: Parser String
pathParser = do
  _ <- string "KEY"
  _ <- string " =" <|> string "="
  _ <- string "" <|> string " "
  path <- manyTill anyChar (string "\n")
  return path

pathParser' :: Parser [String]
pathParser' = endBy pathParser eof

lineParser :: Parser REPLExpr
lineParser = try dumpStateParser
          <|> try showHolesParser
          <|> try loadFileParser
          <|> try addModuleParser
          <|> try reloadFileParser
          <|> try checkTypeParser
          <|> try replDebugger
          <|> try showAstParser
          <|> try runParserRepl
          <|> try runLexer
          -- <|> try unfoldTermParser5
          -- <|> try showASTParser
          <|> evalParser

parseLine :: String -> Either String REPLExpr
parseLine s = case (parse lineParser "" s) of
            Left msg -> Left $ show msg
            Right l -> Right l


textToFilePath :: [T.Text] -> [FilePath]
textToFilePath [] = []
textToFilePath (x:xs) = do
    let spth = T.unpack x
    spth : textToFilePath xs



parsePath :: String -> Either String [String]
parsePath s = do
  case (parse pathParser' "" s) of
    Right l -> Right l
    Left msg -> Left $ show msg
