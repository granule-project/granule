{-#
LANGUAGE
  NoMonomorphismRestriction,
  PackageImports,
  TemplateHaskell,
  FlexibleContexts
#-}
module Repl.ReplParser where

import Prelude
--import Data.List
--import Data.Char
import qualified Data.Text as T
import Text.Parsec
import qualified Text.Parsec.Token as Token
import Text.Parsec.Language
--import Data.Functor.Identity
--import System.FilePath
--import System.Directory
import Syntax.Expr



lexer = haskellStyle {
    Token.reservedOpNames = [":", "let"]
}
tokenizer  = Token.makeTokenParser lexer
reservedOp = Token.reservedOp tokenizer
ws         = Token.whiteSpace tokenizer
symbol     = Token.symbol tokenizer


data REPLExpr =
      Let Id Expr Expr
    | ShowAST Expr
    | DumpState
    | Unfold Expr
    | LoadFile [FilePath]
    | AddModule [FilePath]
    | Reload
    | CheckType String
    | Eval String
    deriving Show

replTermCmdParser short long c p = do
    symbol ":"
    cmd <- many lower
    ws
    t <- p
    eof
    if (cmd == long || cmd == short)
    then return $ c t
    else fail $ "Command \":"++cmd++"\" is unrecognized."

replIntCmdParser short long c = do
    symbol ":"
    cmd <- many lower
    eof
    if (cmd == long || cmd == short)
    then return c
    else fail $ "Command \":"++cmd++"\" is unrecognized."

replTyCmdParser short long c = do
    symbol ":"
    cmd <- many lower
    ws
    term <- many1 anyChar
    eof
    if (cmd == long || cmd == short)
    then return $ c term
    else fail $ "Command \":"++cmd++"\" is unrecognized."

replFileCmdParser short long c = do
    symbol ":"
    cmd <- many lower
    ws
    pathUntrimned <- many1 anyChar
    eof
    if(cmd == long || cmd == short)
    then do
        let tpath = T.words . T.pack $ pathUntrimned
        let fpath = textToFilePath tpath
        return $ c fpath
    else fail $ "Command \":"++cmd++"\" is unrecognized."

evalParser = do
  ev <- many anyChar
  return $ Eval ev
-- showASTParser = replTermCmdParser "s" "show" ShowAST

-- unfoldTermParser = replTermCmdParser "u" "unfold" Unfold

dumpStateParser = replIntCmdParser "d" "dump" DumpState

loadFileParser = replFileCmdParser "l" "load" LoadFile

addModuleParser = replFileCmdParser "m" "module" AddModule

reloadFileParser = replIntCmdParser "r" "reload" Reload

checkTypeParser = replTyCmdParser "t" "type" CheckType




-- lineParser =

lineParser = try dumpStateParser
          <|> try loadFileParser
          <|> try addModuleParser
          <|> try reloadFileParser
          <|> try checkTypeParser
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
