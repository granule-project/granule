{-# 
LANGUAGE 
  NoMonomorphismRestriction, 
  PackageImports, 
  TemplateHaskell, 
  FlexibleContexts 
#-}

module Repl.ReplParser
import Prelude
import Data.List
import Data.Char 
import qualified Data.Text as T
import Text.Parsec 
import qualified Text.Parsec.Token as Token
import Data.Functor.Identity
import System.FilePath
import System.Directory


import Queue
import Syntax.Expr

data REPLExpr = 
      Let Id Expr
    | ShowAST Expr
    | DumpState
    | Unfold Expr
    | Eval Expr
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
    
    
    
showASTParser = replTermCmdParser "s" "show" ShowAST expr    

unfoldTermParser = replTermCmdParser "u" "unfold" Unfold expr

dumpStateParser = replIntCmdParser "d" "dump" DumpState

 