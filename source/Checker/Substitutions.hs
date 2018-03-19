{-# LANGUAGE ImplicitParams #-}

module Checker.Substitutions where

import Control.Monad.State.Strict

import Context
import Syntax.Expr
import Syntax.Pretty
import Checker.Kinds
import Checker.Monad
import Checker.Predicates
import Control.Monad.Trans.Maybe
import Data.Functor.Identity
import Utils

-- For doctest:
-- $setup
-- >>> import Syntax.Expr (mkId)
-- >>> :set -XImplicitParams

{-| Take a context of 'a' and a subhstitution for 'a's (also a context)
  apply the substitution returning a pair of contexts, one for parts
  of the context where a substitution occurred, and one where substitution
  did not occur
>>> let ?globals = defaultGlobals in evalChecker initState (runMaybeT $ substCtxt [(mkId "y", TyInt 0)] [(mkId "x", Linear (TyVar $ mkId "x")), (mkId "y", Linear (TyVar $ mkId "y")), (mkId "z", Discharged (TyVar $ mkId "z") (CVar $ mkId "b"))])
Just ([(Id "y" "y",Linear (TyInt 0))],[(Id "x" "x",Linear (TyVar Id "x" "x")),(Id "z" "z",Discharged (TyVar Id "z" "z") (CVar Id "b" "b"))])
-}

substCtxt :: (?globals :: Globals) => Ctxt Type -> Ctxt Assumption
  -> MaybeT Checker (Ctxt Assumption, Ctxt Assumption)
substCtxt _ [] = return ([], [])
substCtxt subst ((v, x):ctxt) = do
  (substituteds, unsubstituteds) <- substCtxt subst ctxt
  (v', x') <- substAssumption subst (v, x)
  if (v', x') == (v, x)
    then return (substituteds, (v, x) : unsubstituteds)
    else return ((v, x') : substituteds, unsubstituteds)

-- | rewrite a type using a unifier (map from type vars to types)
substType :: Ctxt Type -> Type -> Type
substType ctx = runIdentity .
    typeFoldM (baseTypeFold { tfTyVar = varSubst })
  where
    varSubst v =
       case lookup v ctx of
         Just t -> return t
         Nothing -> mTyVar v

substAssumption :: (?globals :: Globals) => Ctxt Type -> (Id, Assumption)
  -> MaybeT Checker (Id, Assumption)
substAssumption subst (v, Linear t) =
    return $ (v, Linear (substType subst t))
substAssumption subst (v, Discharged t c) = do
    coeffectSubst <- mapMaybeM convertSubst subst
    return $ (v, Discharged (substType subst t) (substCoeffect coeffectSubst c))
  where
    -- Convert a single type substitution (type variable, type pair) into a
    -- coeffect substitution
    convertSubst :: (Id, Type) -> MaybeT Checker (Maybe (Id, Coeffect))
    convertSubst (v, t) = do
      k <- inferKindOfType nullSpan t
      case k of
        KConstr k ->
          case internalName k of
            "Nat=" -> do
              c <- compileNatKindedTypeToCoeffect nullSpan t
              return $ Just (v, c)
            _ -> return Nothing
        _ -> return Nothing
    -- mapM combined with the filtering behaviour of mapMaybe
    mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
    mapMaybeM _ [] = return []
    mapMaybeM f (x:xs) = do
      y <- f x
      ys <- mapMaybeM f xs
      case y of
        Just y' -> return $ y' : ys
        Nothing -> return $ ys

compileNatKindedTypeToCoeffect :: (?globals :: Globals) => Span -> Type -> MaybeT Checker Coeffect
compileNatKindedTypeToCoeffect s (TyInfix op t1 t2) = do
  t1' <- compileNatKindedTypeToCoeffect s t1
  t2' <- compileNatKindedTypeToCoeffect s t2
  case op of
    "+"   -> return $ CPlus t1' t2'
    "*"   -> return $ CTimes t1' t2'
    "\\/" -> return $ CJoin t1' t2'
    "/\\" -> return $ CMeet t1' t2'
    _     -> halt $ UnboundVariableError (Just s) $ "Type-level operator " ++ op
compileNatKindedTypeToCoeffect _ (TyInt n) =
  return $ CNat Discrete n
compileNatKindedTypeToCoeffect _ (TyVar v) =
  return $ CVar v
compileNatKindedTypeToCoeffect s t =
  halt $ KindError (Just s) $ "Type `" ++ pretty t ++ "` does not have kind `Nat=`"

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

substCKind :: Ctxt CKind -> CKind -> CKind
substCKind rmap (CPoly v) =
  case lookup v rmap of
    Nothing -> CPoly v
    Just k  -> k
substCKind rmap c@CConstr{} = c

-- | Apply a name map to a type to rename the type variables
renameType :: [(Id, Id)] -> Type -> Type
renameType rmap t =
    runIdentity $
      typeFoldM (baseTypeFold { tfBox   = renameBox rmap
                              , tfTyVar = renameTyVar rmap }) t
  where
    renameBox renameMap c t = do
      let c' = substCoeffect (map (\(v, var) -> (v, CVar var)) renameMap) c
      let t' = renameType renameMap t
      return $ Box c' t'
    renameTyVar renameMap v =
      case lookup v renameMap of
        Just v' -> return $ TyVar v'
        -- Shouldn't happen
        Nothing -> return $ TyVar v

-- | Get a fresh polymorphic instance of a type scheme and list of instantiated type variables
-- and their new names.
freshPolymorphicInstance :: Quantifier -> TypeScheme -> MaybeT Checker (Type, [Id])
freshPolymorphicInstance quantifier (Forall s kinds ty) = do
    -- Universal becomes an existential (via freshCoeffeVar)
    -- since we are instantiating a polymorphic type
    renameMap <- mapM instantiateVariable kinds
    return $ (renameType renameMap ty, map snd renameMap)

  where
    -- Freshen variables, create existential instantiation
    instantiateVariable (var, k) = do
      -- Freshen the variable depending on its kind
      var' <- case k of
               k | typeBased k -> do
                 freshName <- freshVar (internalName var)
                 let var'  = mkId freshName
                 -- Label fresh variable as an existential
                 modify (\st -> st { tyVarContext = (var', (k, quantifier)) : tyVarContext st })
                 return var'
               KConstr c -> freshCoeffectVarWithBinding var (CConstr c) quantifier
               KCoeffect -> error "Coeffect kind variables not yet supported"
               KPoly _ -> error "Tried to instantiate a polymorphic kind. This is not supported yet.\
               \ Please open an issue with a snippet of your code at https://github.com/dorchard/granule/issues"
      -- Return pair of old variable name and instantiated name (for
      -- name map)
      return (var, var')
    typeBased KType = True
    typeBased (KFun k1 k2) = typeBased k1 && typeBased k2
    typeBased _     = False
