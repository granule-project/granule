-- | Generate fresh symbols.

module Language.Granule.Compiler.Gensym where

import Control.Monad.State
import Data.Functor

-- | The only state required for gensym is a unique number.
newtype GensymState = GensymState { uniqueNum :: Int }
  deriving Show

-- | Generate unique symbols (gensym) by appending a
--   unique number to the end of the symbol string.
--   Requires `GensymState`.
gensym :: MonadState GensymState m => String -> m String
gensym str = do
  n <- get <&> uniqueNum
  put (GensymState $ n + 1)
  return $ str ++ "_" ++ show n

runGensym :: Monad m => StateT GensymState m a -> m a
runGensym c = runStateT c (GensymState 0) <&> fst
