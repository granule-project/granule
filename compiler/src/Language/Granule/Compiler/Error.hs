-- |

module Language.Granule.Compiler.Error where

import Control.Monad.Except
data CompilerError = UnsupportedError String
                   | UnexpectedError  String
                   | OtherError       String

unsupported :: MonadError CompilerError m => String -> m a
unsupported = throwError . UnsupportedError

unexpected :: MonadError CompilerError m => String -> m a
unexpected = throwError . UnexpectedError

instance Show CompilerError where
  show (UnsupportedError str) =
    "Unsupported\n" ++ str
  show (UnexpectedError str) =
    "Unexpected\n" ++ str
  show (OtherError str) =
    str
