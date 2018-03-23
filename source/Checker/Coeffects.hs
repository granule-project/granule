{- Deals with compilation of coeffects into symbolic representations of SBV -}
{-# LANGUAGE ImplicitParams #-}

module Checker.Coeffects where

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

import Checker.Monad
import Checker.Predicates
import Context
import Syntax.Expr
import Syntax.Pretty
import Utils

-- Which coeffects can be flattened
flattenable :: CKind -> Maybe (Coeffect -> Coeffect -> Coeffect)
flattenable (CConstr k) =
  case internalName k of
    "Nat" -> Just CTimes
    "Nat=" -> Just CTimes
    "Nat*" -> Just CTimes
    "Level" -> Just CJoin
    _ -> Nothing
flattenable _ = Nothing

inferCoeffectTypeAssumption :: (?globals :: Globals)
                            => Span -> Assumption -> MaybeT Checker (Maybe CKind)
inferCoeffectTypeAssumption _ (Linear _) = return Nothing
inferCoeffectTypeAssumption s (Discharged _ c) = do
    t <- inferCoeffectType s c
    return $ Just t


-- What is the kind of a particular coeffect?
inferCoeffectType :: (?globals :: Globals) => Span -> Coeffect -> MaybeT Checker CKind

-- Coeffect constants have an obvious kind
inferCoeffectType _ (Level _)         = return $ CConstr $ mkId "Level"
inferCoeffectType _ (CNat Ordered _)  = return $ CConstr $ mkId "Nat"
inferCoeffectType _ (CNat Discrete _) = return $ CConstr $ mkId "Nat="
inferCoeffectType _ (CFloat _)        = return $ CConstr $ mkId "Q"
inferCoeffectType _ (CSet _)          = return $ CConstr $ mkId "Set"
inferCoeffectType _ (CNatOmega _)     = return $ CConstr $ mkId "Nat*"

-- Take the join for compound coeffect epxressions
inferCoeffectType s (CPlus c c')  = mguCoeffectTypes s c c'
inferCoeffectType s (CTimes c c') = mguCoeffectTypes s c c'
inferCoeffectType s (CMeet c c')  = mguCoeffectTypes s c c'
inferCoeffectType s (CJoin c c')  = mguCoeffectTypes s c c'

-- Coeffect variables should have a kind in the cvar->kind context
inferCoeffectType s (CVar cvar) = do
  checkerState <- get
  liftIO $ putStrLn $ "Looking for " ++ show cvar ++ " in  " ++ show (tyVarContext checkerState)
  case lookup cvar (tyVarContext checkerState) of
     Nothing -> do
       halt $ UnboundVariableError (Just s) $ "Tried to lookup kind of " ++ pretty cvar
--       state <- get
--       let newCKind = CPoly $ "ck" ++ show (uniqueVarId state)
       -- We don't know what it is yet though, so don't update the coeffect kind ctxt
--       put (state { uniqueVarId = uniqueVarId state + 1 })
--       return newCKind

     Just (KConstr name, _) -> checkKind s (CConstr name)


     Just (KPoly   name, _) -> return $ CPoly name
     Just (k, _)            -> illKindedNEq s KCoeffect k

inferCoeffectType s (CZero k) = checkKind s k
inferCoeffectType s (COne k)  = checkKind s k
inferCoeffectType s (CInfinity k)  = checkKind s k
inferCoeffectType s (CSig _ k) = checkKind s k

checkKind s k@(CConstr name) = do
  st <- get
  case lookup name (typeConstructors st) of
    Just KCoeffect -> return $ CConstr name
    Just _         -> illKindedNEq s KCoeffect (KConstr name)
    _              ->
      halt $ UnboundVariableError (Just s) $ "Type `" ++ pretty name ++ "`"
checkKind _ k = return k

-- Given a coeffect type variable and a coeffect kind,
-- replace any occurence of that variable in an context
-- and update the current solver predicate as well
updateCoeffectKind :: Id -> Kind -> MaybeT Checker ()
updateCoeffectKind tyVar kind = do
    modify (\checkerState ->
     checkerState
      { tyVarContext = rewriteCtxt (tyVarContext checkerState),
        kVarContext = replace (kVarContext checkerState) tyVar kind })
  where
    rewriteCtxt :: Ctxt (Kind, Quantifier) -> Ctxt (Kind, Quantifier)
    rewriteCtxt [] = []
    rewriteCtxt ((name, (KPoly kindVar, q)) : ctxt)
     | tyVar == kindVar = (name, (kind, q)) : rewriteCtxt ctxt
    rewriteCtxt (x : ctxt) = x : rewriteCtxt ctxt

-- Find the most general unifier of two coeffects
-- This is an effectful operation which can update the coeffect-kind
-- contexts if a unification resolves a variable
mguCoeffectTypes :: (?globals :: Globals) => Span -> Coeffect -> Coeffect -> MaybeT Checker CKind
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

    (CConstr k1, CConstr k2) | internalName k1 == "Nat=" && internalName k2 == "Nat"
      -> return $ CConstr $ mkId "Nat="

    (CConstr k1, CConstr k2) | internalName k1 == "Nat" && internalName k2 == "Nat="
      -> return $ CConstr $ mkId "Nat="

    (CConstr k1, CConstr k2) | k1 == k2 -> return $ CConstr k1

    (CConstr k1, CConstr k2) | Just ck <- joinCoeffectConstr k1 k2 ->
      return $ CConstr ck

    (k1, k2) -> halt $ KindError (Just s) $ "Cannot unify coeffect types '"
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


joinCoeffectConstr :: Id -> Id -> Maybe Id
joinCoeffectConstr k1 k2 = fmap mkId $ go (internalName k1) (internalName k2)
  where
    --go "Nat" n | "Nat" `isPrefixOf` n = Just n
    --go n "Nat" | "Nat" `isPrefixOf` n = Just n
    go "Float" "Nat" = Just "Float"
    go "Nat" "Float" = Just "Float"
    go k k' | k == k' = Just k
    go _ _ = Nothing
