{-# LANGUAGE FlexibleContexts #-}
module Language.Granule.ReplError where

import Control.Monad.Except()
import Control.Exception (SomeException)


data ReplError = FilePathError String
               | TermInContext String
               | OtherError
               | OtherError'
               -- TypeCheckError and ParserError record the filepath queue
               -- so that reloading across files can be done even if we
               -- fail to load a file the first time
               | TypeCheckError String [FilePath] -- FilePath queue
               | ParseError SomeException [FilePath] -- FilePath queue
               | TermNotInContext String
               | EvalError SomeException

remembersFiles :: ReplError -> Maybe [FilePath]
remembersFiles (ParseError _ f) = Just f
remembersFiles (TypeCheckError _ f) = Just f
remembersFiles _ = Nothing

instance Show ReplError where
  show (FilePathError pth)    = "The file path "<>pth<>" does not exist."
  show (TermInContext trm)    = "The term \""<>trm<>"\" is already in context"
  show (TypeCheckError pth _)   = "Error type checking "<>pth
  show (ParseError e _)         = show e
  show (TermNotInContext trm) = "The term \""<>trm<>"\" is not in the context"
  show (EvalError e)          = show e
  show OtherError             = "Error"
  show OtherError'            = ""
