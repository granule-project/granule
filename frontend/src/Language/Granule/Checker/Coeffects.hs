{- Deals with coeffect resource algebras -}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Coeffects where

import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Monad
import Language.Granule.Context

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Utils

-- | Multiply an context by a coeffect
--   (Derelict and promote all variables which are not discharged and are in th
--    set of used variables, (first param))
multAll :: (?globals :: Globals) => Span -> [Id] -> Coeffect -> Ctxt Assumption -> Checker (Ctxt Assumption)

multAll _ _ _ [] = return []

multAll s vars c ((name, Linear t) : ctxt) | name `elem` vars = do
    ctxt' <- multAll s vars c ctxt
    return $ (name, Discharged t c) : ctxt'

multAll s vars c ((name, Discharged t c') : ctxt) | name `elem` vars = do
    ctxt' <- multAll s vars c ctxt
    -- TODO: do we want to throw away the subst?
    (_, _, (inj1, inj2)) <- mguCoeffectTypesFromCoeffects s c c'
    return $ (name, Discharged t ((inj1 c) `CTimes` (inj2 c'))) : ctxt'

-- Ignore linear and non-relevant variables
multAll s vars c ((_, Linear _) : ctxt) =
    multAll s vars c ctxt

multAll s vars c ((_, Discharged _ _) : ctxt) =
    multAll s vars c ctxt