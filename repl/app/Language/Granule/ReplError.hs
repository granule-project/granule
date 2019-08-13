{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}

module Language.Granule.ReplError where

import Control.Monad.Except()
import Control.Exception (SomeException)
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty)
import Data.Foldable (toList)

import Language.Granule.Checker.Monad (CheckerError)
import Language.Granule.Utils (formatError)

data ReplError = FilePathError String
               | TermInContext String
               | OtherError
               -- TypeCheckError and ParserError record the filepath queue
               -- so that reloading across files can be done even if we
               -- fail to load a file the first time
               | TypeCheckerError (NonEmpty CheckerError) [FilePath]
               | ParseError SomeException [FilePath] -- FilePath queue
               | ParseError' String

               | TermNotInContext String
               | EvalError SomeException

remembersFiles :: ReplError -> Maybe [FilePath]
remembersFiles (ParseError _ f)       = Just f
remembersFiles (TypeCheckerError _ f) = Just f
remembersFiles _ = Nothing

instance Show ReplError where
  show (FilePathError pth)    = "The file `"<>pth<>"` does not exist."
  show (TermInContext trm)    = "The term `"<>trm<>"` is already in context"
  show (ParseError e _)       = show e
  show (ParseError' msg)      = msg
  show (TermNotInContext trm) = "The term `"<>trm<>"` is not in the context"
  show (EvalError e)          = show e
  show OtherError             = "Error"
  show (TypeCheckerError err _) = let ?globals = mempty in intercalate "\n\n" . map formatError . toList $ err
