{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}

module Language.Granule.Interpreter.Config where

import Control.Applicative
-- import Data.Functor.Classes (Read1) -- (Eq1, Read1, Show1)
import Data.Functor.Identity

import qualified Language.Granule.Utils as Utils (Globals(..))

data Options (f :: * -> *)
  = Options
    { debugging           :: f Bool
    , timing              :: f Bool
    , noColors            :: f Bool
    , noEval              :: f Bool
    , suppressInfos       :: f Bool
    , suppressErrors      :: f Bool
    , timestamp           :: f Bool
    , solverTimeoutMillis :: f Integer
    , includePath         :: f FilePath
    , ascii2unicode       :: f Bool
    , keepBackupAscii     :: f Bool
    }

-- deriving instance Show1 f => Show (Options f)
-- deriving instance Eq1   f => Eq   (Options f)
-- deriving instance Read1 f => Read (Options f)

deriving instance Read (Options Maybe)
deriving instance Show (Options Identity)
deriving instance Show (Options Maybe)

-- TODO make more general
defaultConfig :: Options Maybe -> Options Identity
defaultConfig o = Options
  { debugging           = maybe (Identity False) Identity $ debugging o
  , timing              = maybe (Identity False) Identity $ timing o
  , noColors            = maybe (Identity False) Identity $ noColors o
  , noEval              = maybe (Identity False) Identity $ noEval o
  , suppressInfos       = maybe (Identity False) Identity $ suppressInfos o
  , suppressErrors      = maybe (Identity False) Identity $ suppressErrors o
  , timestamp           = maybe (Identity False) Identity $ timestamp o
  , solverTimeoutMillis = maybe (Identity 5000) Identity $ solverTimeoutMillis o
  , includePath         = maybe (Identity "StdLib") Identity $ includePath o
  , ascii2unicode       = maybe (Identity False) Identity $ ascii2unicode o
  , keepBackupAscii     = maybe (Identity True) Identity $ keepBackupAscii o
  }

instance Alternative f => Semigroup (Options f) where
  o1 <> o2 = Options
      { debugging           = debugging           o1 <|> debugging           o2
      , timing              = timing              o1 <|> timing              o2
      , noColors            = noColors            o1 <|> noColors            o2
      , noEval              = noEval              o1 <|> noEval              o2
      , suppressInfos       = suppressInfos       o1 <|> suppressInfos       o2
      , suppressErrors      = suppressErrors      o1 <|> suppressErrors      o2
      , timestamp           = timestamp           o1 <|> timestamp           o2
      , solverTimeoutMillis = solverTimeoutMillis o1 <|> solverTimeoutMillis o2
      , includePath         = includePath         o1 <|> includePath         o2
      , ascii2unicode       = ascii2unicode       o1 <|> ascii2unicode       o2
      , keepBackupAscii     = keepBackupAscii     o1 <|> keepBackupAscii     o2

      }

instance Alternative f => Monoid (Options f) where
  mempty = Options
      { debugging           = empty
      , timing              = empty
      , noColors            = empty
      , noEval              = empty
      , suppressInfos       = empty
      , suppressErrors      = empty
      , timestamp           = empty
      , solverTimeoutMillis = empty
      , includePath         = empty
      , ascii2unicode       = empty
      , keepBackupAscii     = empty
      }

toGlobals :: FilePath -> Options Identity -> Utils.Globals
toGlobals fp o = Utils.Globals
    { Utils.debugging           = runIdentity $ debugging           o
    , Utils.timing              = runIdentity $ timing              o
    , Utils.noColors            = runIdentity $ noColors            o
    , Utils.noEval              = runIdentity $ noEval              o
    , Utils.suppressInfos       = runIdentity $ suppressInfos       o
    , Utils.suppressErrors      = runIdentity $ suppressErrors      o
    , Utils.timestamp           = runIdentity $ timestamp           o
    , Utils.solverTimeoutMillis = runIdentity $ solverTimeoutMillis o
    , Utils.includePath         = runIdentity $ includePath         o
    , Utils.sourceFilePath      = fp
    }
