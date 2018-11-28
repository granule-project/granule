module Language.Granule.TestUtils where

import Language.Granule.Utils (Globals(..))

defaultGlobals :: Globals
defaultGlobals =
    Globals
    { debugging = False
    , sourceFilePath = ""
    , noColors = False
    , noEval = False
    , suppressInfos = False
    , suppressErrors = False
    , timestamp = False
    , solverTimeoutMillis = Just 1000
    }
