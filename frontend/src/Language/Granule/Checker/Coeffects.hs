{- Deals with compilation of coeffects into symbolic representations of SBV -}
{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.Coeffects where

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

import Language.Granule.Checker.Monad
import Language.Granule.Context
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Utils

-- Which coeffects can be flattened
flattenable :: Type -> Maybe (Coeffect -> Coeffect -> Coeffect)
flattenable (TyCon k) =
  case internalName k of
    "Nat" -> Just CTimes
    "Nat=" -> Just CTimes
    "Nat*" -> Just CTimes
    "Level" -> Just CJoin
    _ -> Nothing
flattenable _ = Nothing

checkKind :: (?globals :: Globals) => Span -> Type -> MaybeT Checker Type
checkKind s k@(TyCon name) = do
  st <- get
  case lookup name (typeConstructors st) of
    Just (KCoeffect,_) -> return $ TyCon name
    Just _             -> illKindedNEq s KCoeffect (KConstr name)
    _                  ->
      halt $ UnboundVariableError (Just s) $ "Type `" <> pretty name <> "`"
checkKind _ k = return k

-- | Multiply an context by a coeffect
--   (Derelict and promote all variables which are not discharged and are in th
--    set of used variables, (first param))
multAll :: [Id] -> Coeffect -> Ctxt Assumption -> Ctxt Assumption

multAll _ _ [] = []

multAll vars c ((name, Linear t) : ctxt) | name `elem` vars
    = (name, Discharged t c) : multAll vars c ctxt

multAll vars c ((name, Discharged t c') : ctxt) | name `elem` vars
    = (name, Discharged t (c `CTimes` c')) : multAll vars c ctxt

multAll vars c ((_, Linear _) : ctxt) = multAll vars c ctxt
multAll vars c ((_, Discharged _ _) : ctxt) = multAll vars c ctxt