{-# LANGUAGE FlexibleContexts #-}
module Language.Granule.Codegen.Emit.EmitterState where

import Language.Granule.Syntax.Identifiers (Id, internalName)
import Control.Monad.State.Strict hiding (void)

import LLVM.AST (Operand)

import Data.Map (Map, insertWith)
import qualified Data.Map as Map

data EmitterState = EmitterState {
    localSymbols :: Map Id Operand
}

addLocal name operand =
    modify $ \s -> s { localSymbols =
                           insertWith (\_ _ -> error "Unexpected name shadowing")
                                      name operand (localSymbols s) }

clearLocals :: (MonadState EmitterState m)
            => m ()
clearLocals =
    modify $ \s -> s { localSymbols = Map.empty }

{-lookupConstrPrimative :: (MonadState EmitterState m)
                      => String
                      -> m (Maybe Operand)
lookupConstrPrimative name =
    gets $ snd . (Map.lookup name) -}

local :: (MonadState EmitterState m)
      => Id
      -> m Operand
local name =
    do
        local <- gets ((Map.lookup name) . localSymbols)
        case local of
            Just op -> return op
            Nothing -> error $ internalName name ++ " registered as a local, missing call to addLocal?\n"
