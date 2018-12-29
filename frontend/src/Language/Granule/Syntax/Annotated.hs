{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Granule.Syntax.Annotated where

class Annotated t a where
    annotation :: t -> a
