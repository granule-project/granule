{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
module Language.Granule.Codegen.Emit.MkId where

import Language.Granule.Syntax.Identifiers

pattern MkId s <- (internalName -> s) where
    MkId s = Id s s
