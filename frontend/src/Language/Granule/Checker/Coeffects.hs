{- Deals with coeffect resource algebras -}
{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.Coeffects where

import Language.Granule.Checker.Monad
import Language.Granule.Checker.SubstitutionAndKinding
import Language.Granule.Context

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Utils

-- Calculate whether a coeffect expression could be used for any semiring
isGenericCoeffectExpression :: Type -> Bool
isGenericCoeffectExpression (TyInt 1) = True
isGenericCoeffectExpression (TyInt 0) = True
isGenericCoeffectExpression (TyInfix TyOpPlus c1 c2) =
  isGenericCoeffectExpression c1 && isGenericCoeffectExpression c2
isGenericCoeffectExpression (TyInfix TyOpTimes c1 c2) =
  isGenericCoeffectExpression c1 && isGenericCoeffectExpression c2
isGenericCoeffectExpression (TyInfix TyOpMeet c1 c2) =
  isGenericCoeffectExpression c1 && isGenericCoeffectExpression c2
isGenericCoeffectExpression (TyInfix TyOpJoin c1 c2) =
  isGenericCoeffectExpression c1 && isGenericCoeffectExpression c2
isGenericCoeffectExpression _ = False

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
