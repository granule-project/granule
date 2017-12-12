{- Deals with compilation of coeffects into symbolic representations of SBV -}

module Checker.Coeffects where

import Data.List (isPrefixOf)

import Context
import Syntax.Expr
import Syntax.Pretty

import Checker.Kinds
import Checker.Monad
import Checker.Predicates

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

-- Which coeffects can be flattened
flattenable :: CKind -> Maybe (Coeffect -> Coeffect -> Coeffect)
flattenable (CConstr "Nat")  = Just CTimes
flattenable (CConstr "Nat=") = Just CTimes
flattenable (CConstr "Nat*") = Just CTimes
flattenable (CConstr "Level") = Just CJoin
flattenable _                 = Nothing

-- What is the kind of a particular coeffect?
inferCoeffectType :: Span -> Coeffect -> MaybeT Checker CKind

-- Coeffect constants have an obvious kind
inferCoeffectType _ (Level _)         = return $ CConstr "Level"
inferCoeffectType _ (CNat Ordered _)  = return $ CConstr "Nat"
inferCoeffectType _ (CNat Discrete _) = return $ CConstr "Nat="
inferCoeffectType _ (CFloat _)        = return $ CConstr "Q"
inferCoeffectType _ (CSet _)          = return $ CConstr "Set"
inferCoeffectType _ (CNatOmega _)     = return $ CConstr "Nat*"

-- Take the join for compound coeffect epxressions
inferCoeffectType s (CPlus c c')  = mguCoeffectTypes s c c'
inferCoeffectType s (CTimes c c') = mguCoeffectTypes s c c'
inferCoeffectType s (CMeet c c')  = mguCoeffectTypes s c c'
inferCoeffectType s (CJoin c c')  = mguCoeffectTypes s c c'

-- Coeffect variables should have a kind in the cvar->kind context
inferCoeffectType s (CVar cvar) = do
  checkerState <- get
  case lookup cvar (ckctxt checkerState) of
     Nothing -> do
       unknownName s $ "Tried to lookup kind of " ++ cvar
--       state <- get
--       let newCKind = CPoly $ "ck" ++ show (uniqueVarId state)
       -- We don't know what it is yet though, so don't update the coeffect kind ctxt
--       put (state { uniqueVarId = uniqueVarId state + 1 })
--       return newCKind

     Just (KConstr name, _) -> return $ CConstr name
     Just (KPoly   name, _) -> return $ CPoly name
     Just (k, _)            -> illKindedNEq s KCoeffect k

inferCoeffectType _ (CZero k) = return k
inferCoeffectType _ (COne k)  = return k
inferCoeffectType _ (CInfinity k)  = return k
inferCoeffectType _ (CSig _ k) = return k

-- Given a coeffect type variable and a coeffect kind,
-- replace any occurence of that variable in an context
-- and update the current solver predicate as well
updateCoeffectKind :: Id -> Kind -> MaybeT Checker ()
updateCoeffectKind tyVar kind = do
    checkerState <- get
    put $ checkerState
      { ckctxt = rewriteCtxt (ckctxt checkerState),
        cVarCtxt = replace (cVarCtxt checkerState) tyVar kind }
  where
    rewriteCtxt :: Ctxt (Kind, Quantifier) -> Ctxt (Kind, Quantifier)
    rewriteCtxt [] = []
    rewriteCtxt ((name, (KPoly kindVar, q)) : ctxt)
     | tyVar == kindVar = (name, (kind, q)) : rewriteCtxt ctxt
    rewriteCtxt (x : ctxt) = x : rewriteCtxt ctxt

-- Find the most general unifier of two coeffects
-- This is an effectful operation which can update the coeffect-kind
-- contexts if a unification resolves a variable
mguCoeffectTypes :: Span -> Coeffect -> Coeffect -> MaybeT Checker CKind
mguCoeffectTypes s c1 c2 = do
  ck1 <- inferCoeffectType s c1
  ck2 <- inferCoeffectType s c2
  case (ck1, ck2) of
    -- Both are poly
    (CPoly kv1, CPoly kv2) -> do
      updateCoeffectKind kv1 (liftCoeffectType $ CPoly kv2)
      return (CPoly kv2)

   -- Linear-hand side is a poly variable, but right is concrete
    (CPoly kv1, ck2') -> do
      updateCoeffectKind kv1 (liftCoeffectType ck2')
      return ck2'

    -- Right-hand side is a poly variable, but Linear is concrete
    (ck1', CPoly kv2) -> do
      updateCoeffectKind kv2 (liftCoeffectType ck1')
      return ck1'

    (CConstr k1, CConstr k2) | k1 == k2 -> return $ CConstr k1

    (CConstr k1, CConstr k2) | Just ck <- joinCoeffectConstr k1 k2 ->
      return $ CConstr ck

    (k1, k2) -> do
      illTyped s $ "Cannot unify coeffect types '"
               ++ pretty k1 ++ "' and '" ++ pretty k2
               ++ "' for coeffects " ++ pretty c1 ++ " and " ++ pretty c2

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

{- | Perform a substitution on a coeffect based on a context mapping
     variables to coeffects -}
substCoeffect :: Ctxt Coeffect -> Coeffect -> Coeffect
substCoeffect rmap (CPlus c1 c2) = let
    c1' = substCoeffect rmap c1
    c2' = substCoeffect rmap c2
    in CPlus c1' c2'

substCoeffect rmap (CJoin c1 c2) = let
    c1' = substCoeffect rmap c1
    c2' = substCoeffect rmap c2
    in CJoin c1' c2'

substCoeffect rmap (CMeet c1 c2) = let
    c1' = substCoeffect rmap c1
    c2' = substCoeffect rmap c2
    in CMeet c1' c2'

substCoeffect rmap (CTimes c1 c2) = let
    c1' = substCoeffect rmap c1
    c2' = substCoeffect rmap c2
    in CTimes c1' c2'

substCoeffect rmap (CVar v) =
    case lookup v rmap of
      Just c  -> c
      Nothing -> CVar v

substCoeffect _ c@CNat{}   = c
substCoeffect _ c@CNatOmega{} = c
substCoeffect _ c@CFloat{} = c
substCoeffect _ c@CInfinity{}  = c
substCoeffect _ c@COne{}   = c
substCoeffect _ c@CZero{}  = c
substCoeffect _ c@Level{}  = c
substCoeffect _ c@CSet{}   = c
substCoeffect _ c@CSig{}   = c