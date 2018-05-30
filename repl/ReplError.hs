{-# LANGUAGE FlexibleContexts #-}
module ReplError where

import Control.Monad.Except()
import Control.Exception (SomeException)


data ReplError = FilePathError String
               | TermInContext String
               | OtherError
               | OtherError'
               | TypeCheckError String
               | ParseError SomeException
               | TermNotInContext String
               | EvalError SomeException

instance Show ReplError where
  show (FilePathError pth)    = "The file path "++pth++" does not exist."
  show (TermInContext trm)    = "The term \""++trm++"\" is already in context"
  show (TypeCheckError pth)   = "Error type checking "++pth
  show (ParseError e)         = show e
  show (TermNotInContext trm) = "The term \""++trm++"\" is not in the context"
  show (EvalError e)          = show e
  show OtherError             = "Error"
  show OtherError'            = ""
