{- Deals with compilation of coeffects into symbolic representations of SBV -}

module Checker.Coeffects where

import Checker.Monad
import Context
import Syntax.Expr
import Syntax.Pretty

import Checker.Constraints (Quantifier)
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
kindOf :: Span -> Coeffect -> MaybeT Checker CKind

-- Coeffect constants have an obvious kind
kindOf _ (Level _)         = return $ CConstr "Level"
kindOf _ (CNat Ordered _)  = return $ CConstr "Nat"
kindOf _ (CNat Discrete _) = return $ CConstr "Nat="
kindOf _ (CFloat _)        = return $ CConstr "Q"
kindOf _ (CSet _)          = return $ CConstr "Set"
kindOf _ (CNatOmega _)     = return $ CConstr "Nat*"

-- Take the join for compound coeffect epxressions
kindOf s (CPlus c c')  = mguCoeffectKinds s c c'
kindOf s (CTimes c c') = mguCoeffectKinds s c c'
kindOf s (CMeet c c')  = mguCoeffectKinds s c c'
kindOf s (CJoin c c')  = mguCoeffectKinds s c c'

-- Coeffect variables should have a kind in the cvar->kind context
kindOf s (CVar cvar) = do
  checkerState <- get
  case lookup cvar (ckctxt checkerState) of
     Nothing -> do
       unknownName s $ "Tried to lookup kind of " ++ cvar
--       state <- get
--       let newCKind = CPoly $ "ck" ++ show (uniqueVarId state)
       -- We don't know what it is yet though, so don't update the coeffect kind ctxt
--       put (state { uniqueVarId = uniqueVarId state + 1 })
--       return newCKind

     Just (k, _) -> return k

kindOf _ (CZero k) = return k
kindOf _ (COne k)  = return k
kindOf _ (CStar k)  = return k
kindOf _ (CSig _ k) = return k

-- Given a coeffect kind variable and a coeffect kind,
-- replace any occurence of that variable in an context
-- and update the current solver predicate as well
updateCoeffectKind :: Id -> CKind -> MaybeT Checker ()
updateCoeffectKind ckindVar ckind = do
    checkerState <- get
    put $ checkerState
      { ckctxt = rewriteCtxt (ckctxt checkerState),
        cVarCtxt = replace (cVarCtxt checkerState) ckindVar ckind }
  where
    rewriteCtxt :: Ctxt (CKind, Quantifier) -> Ctxt (CKind, Quantifier)
    rewriteCtxt [] = []
    rewriteCtxt ((name, (CPoly ckindVar', q)) : ctxt)
     | ckindVar == ckindVar' = (name, (ckind, q)) : rewriteCtxt ctxt
    rewriteCtxt (x : ctxt) = x : rewriteCtxt ctxt

-- Find the most general unifier of two coeffects
-- This is an effectful operation which can update the coeffect-kind
-- contexts if a unification resolves a variable
mguCoeffectKinds :: Span -> Coeffect -> Coeffect -> MaybeT Checker CKind
mguCoeffectKinds s c1 c2 = do
  ck1 <- kindOf s c1
  ck2 <- kindOf s c2
  case (ck1, ck2) of
    -- Both are poly
    (CPoly kv1, CPoly kv2) -> do
      updateCoeffectKind kv1 (CPoly kv2)
      return (CPoly kv2)

   -- Linear-hand side is a poly variable, but right is concrete
    (CPoly kv1, ck2') -> do
      updateCoeffectKind kv1 ck2'
      return ck2'

    -- Right-hand side is a poly variable, but Linear is concrete
    (ck1', CPoly kv2) -> do
      updateCoeffectKind kv2 ck1'
      return ck1'

    (CConstr k1, CConstr k2) | k1 == k2 -> return $ CConstr k1

    (CConstr "Nat*", CConstr "Nat")     -> return $ CConstr "Nat*"
    (CConstr "Nat", CConstr "Nat*")     -> return $ CConstr "Nat*"

    (CConstr "Nat", CConstr "Float")     -> return $ CConstr "Float"
    (CConstr "Float", CConstr "Nat")     -> return $ CConstr "Float"
    (k1, k2) -> do
      -- c2' <- renameC s (map (\(a, b) -> (b, a)) nameMap) c2
      -- c1' <- renameC s (map (\(a, b) -> (b, a)) nameMap) c1
      illTyped s $ "Cannot unify coeffect types of '" ++ pretty k1 ++ "' and '" ++ pretty k2
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

-- | Perform a renaming on a coeffect
renameC :: Span -> Ctxt Id -> Coeffect -> MaybeT Checker Coeffect
renameC s rmap (CPlus c1 c2) = do
      c1' <- renameC s rmap c1
      c2' <- renameC s rmap c2
      return $ CPlus c1' c2'

renameC s rmap (CTimes c1 c2) = do
      c1' <- renameC s rmap c1
      c2' <- renameC s rmap c2
      return $ CTimes c1' c2'

renameC s rmap (CVar v) =
      case lookup v rmap of
        Just v' -> return $ CVar v'
        Nothing -> illTyped s $ "Coeffect variable " ++ v ++ " is unbound"

renameC _ _ c = return c
