{- Deals with coeffect algebras -}
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

-- | Find out whether a coeffect if flattenable, and if so get the operation
-- | used to representing flattening on the grades
flattenable :: Type -> Type -> Maybe ((Coeffect -> Coeffect -> Coeffect), Type)
flattenable t1 t2
 | t1 == t2 = case t1 of
     t1 | t1 == extendedNat -> Just (CTimes, t1)

     TyCon (internalName -> "Nat")   -> Just (CTimes, t1)
     TyCon (internalName -> "Level") -> Just (CMeet, t1)

     -- TODO
     TyApp (TyCon (internalName -> "Interval")) t ->  flattenable t t

     _ -> Nothing
 | otherwise =
     case (t1, t2) of
        (t1, TyCon (internalName -> "Nat")) | t1 == extendedNat -> Just (CTimes, t1)
        (TyCon (internalName -> "Nat"), t2) | t2 == extendedNat -> Just (CTimes, t2)

        _ -> Just (CProduct, TyCon (mkId "×") .@ t1 .@ t2)

-- | Multiply an context by a coeffect (algorithmic-style)
--   (Derelict and promote all variables which are not discharged and are in the
--    set of used variables, (first param))
multAll :: (?globals :: Globals) => Span -> [Id] -> Coeffect -> Ctxt Assumption -> Checker (Ctxt Assumption)

multAll _ _ _ [] = return []

multAll s vars c ((name, Linear t) : ctxt) | name `elem` vars = do
    ctxt' <- multAll s vars c ctxt
    return $ (name, Discharged t c) : ctxt'

multAll s vars c ((name, Discharged t c') : ctxt) | name `elem` vars = do
    ctxt' <- multAll s vars c ctxt
    (_, (inj1, inj2)) <- mguCoeffectTypes s c c'
    return $ (name, Discharged t ((inj1 c) `CTimes` (inj2 c'))) : ctxt'

-- Ignore linear and non-relevant variables
multAll s vars c ((_, Linear _) : ctxt) =
    multAll s vars c ctxt

multAll s vars c ((_, Discharged _ _) : ctxt) =
    multAll s vars c ctxt