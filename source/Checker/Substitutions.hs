{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Checker.Substitutions where

import Control.Monad.State.Strict

import Context
import Syntax.Expr
import Syntax.Pretty
import Checker.Kinds
import Checker.Monad
import Checker.Predicates
import Control.Monad.Trans.Maybe
import Utils

-- For doctest:
-- $setup
-- >>> import Syntax.Expr (mkId)
-- >>> :set -XImplicitParams

{-| Substitutions map from variables to type-level things as defined by
    substitutors -}
type Substitution = Ctxt Substitutors

{-| Substitutors are things we want to substitute in... they may be one
     of several things... -}
data Substitutors =
    SubstT  Type
  | SubstC  Coeffect
  | SubstK  Kind
  | SubstCK CKind
  | SubstE  Effect
  deriving Show

class Substitutable t where
  -- | Rewrite a 't' using a substitution
  type SubstitutionContext t x
  substitute :: (?globals :: Globals) => Substitution -> t -> SubstitutionContext t t

  unify :: t -> t -> SubstitutionContext t (Maybe Substitution)

-- Instances for the main representation of things in the types

instance Substitutable Substitutors where
  type SubstitutionContext Substitutors x = MaybeT Checker x
  substitute subst s =
    case s of
      SubstT t -> do
        t <- substitute subst t
        return $ SubstT t

      SubstC c -> do
        c <- substitute subst c
        return $ SubstC c

      SubstK k ->
        return $ SubstK (substitute subst k)

      SubstCK k ->
        return $ SubstCK (substitute subst k)

      SubstE e -> do
        e <- substitute subst e
        return $ SubstE e

  unify (SubstT t) (SubstT t') = return $ unify t t'
  unify (SubstT t) (SubstC c') = do
    -- We can unify a type with a coeffect, if the type is actually a Nat=
    k <- inferKindOfType nullSpan t
    case k of
      KConstr k | internalName k == "Nat=" -> do
             c <- compileNatKindedTypeToCoeffect nullSpan t
             unify c c'
      _ -> return Nothing
  unify (SubstC c') (SubstT t) = unify (SubstT t) (SubstC c')
  unify (SubstC c) (SubstC c') = unify c c'
  unify (SubstK k) (SubstK k') = unify k k'
  unify (SubstCK k) (SubstCK k') = unify k k'
  unify (SubstE e) (SubstE e') = unify e e'
  unify _ _ = Nothing

<++> :: Maybe [a] -> Maybe [a] -> Maybe [a]
xs <++> ys = xs >>= (\xs' -> ys >>= (\ys' -> return $ xs' ++ ys'))

instance Substitutable Type where
  type SubstitutionContext Type x = MaybeT Checker x
  substitute subst = typeFoldM (baseTypeFold
                              { tfTyVar = varSubst
                              , tfBox = box
                              , tfDiamond = dia })
    where
      box c t = do
        c <- substitute subst c
        t <- substitute subst t
        mBox c t

      dia e t = do
        e <- substitute subst e
        t <- substitute subst t
        mDiamond e t

      varSubst v =
         case lookup v subst of
           Just (SubstT t) -> return t
           _               -> mTyVar v

  unify (TyVar v) t' = return $ Just [(v, SubstT t)]
  unify t (TyVar v)  = return $ Just [(v, SubstT t)]
  unify (FunTy t1 t2) (FunTy t1' t2') = do
    u1 <- unify t1 t1'
    u2 <- unify t2 t2'
    return $ u1 <++> u2
  unify (TyCon c) (TyCon c') | c == c' = return $ Just []
  unify (Box c t) (Box c' t') = do
    u1 <- unify c c'
    u2 <- unify t t'
    return $ u1 <++> u2
  unify (Diamond e t) (Diamond e' t') = do
    u1 <- unify e e'
    u2 <- unify t t'
    return $ u1 <++> u2
  unify (TyApp t1 t2) (TyApp t1' t2') = do
    u1 <- unify t1 t1'
    u2 <- unify t2 t2'
    return $ u1 <++> u2
  unify (TyInt i) (TyInt j) | i == j = return $ Just []
  unify (PairTy t1 t2) (PairTy t1' t2') = do
    u1 <- unify t1 t1'
    u2 <- unify t2 t2'
    return $ u1 <++> u2
  unify t@(TyInfix o t1 t2) t'@(TyInfix o' t1 t2') = do
    k <- inferKindOfType nullSpan t
    case k of
      KConstr k | internalName k == "Nat=" -> do
        c <- compileNatKindedTypeToCoeffect nullSpan t
        c' <- compileNatKindedTypeToCoeffect nullSpan t'
        addConstraint $ Eq nullSpan c c'
        return $ Just []
      _ | o == o' -> do
        u1 <- unify t1 t1'
        u2 <- unify t2 t2'
        return $ u1 <++> u2
      -- No unification
      _ -> return $ Nothing
  -- No unification
  unify _ _ = return $ Nothing

instance Substitutable Coeffect where
  type SubstitutionContext Coeffect x = MaybeT Checker x

  substitute subst (CPlus c1 c2) = do
      c1' <- substitute subst c1
      c2' <- substitute subst c2
      return $ CPlus c1' c2'

  substitute subst (CJoin c1 c2) = do
      c1' <- substitute subst c1
      c2' <- substitute subst c2
      return $ CJoin c1' c2'

  substitute subst (CMeet c1 c2) = do
      c1' <- substitute subst c1
      c2' <- substitute subst c2
      return $ CMeet c1' c2'

  substitute subst (CTimes c1 c2) = do
      c1' <- substitute subst c1
      c2' <- substitute subst c2
      return $ CTimes c1' c2'

  substitute subst (CVar v) =
      case lookup v subst of
        Just (SubstC c) -> return c
        -- Convert a single type substitution (type variable, type pair) into a
        -- coeffect substituion
        Just (SubstT t) -> do
          k <- inferKindOfType nullSpan t
          case k of
            KConstr k ->
              case internalName k of
                "Nat=" -> compileNatKindedTypeToCoeffect nullSpan t
                _      -> return (CVar v)
            _ -> return (CVar v)

        _               -> return $ CVar v

  substitute subst (CInfinity k) = return $
    CInfinity (substitute subst k)

  substitute subst (COne k) = return $
    COne (substitute subst k)

  substitute subst (CZero k) = return $
    CZero (substitute subst k)

  substitute subst (CSet tys) = do
    tys <- mapM (\(v, t) -> substitute subst t >>= (\t' -> return (v, t'))) tys
    return $ CSet tys

  substitute subst (CSig c k) = do
    c <- substitute subst c
    return $ CSig c (substitute subst k)

  substitute _ c@CNat{}      = return c
  substitute _ c@CNatOmega{} = return c
  substitute _ c@CFloat{}    = return c
  substitute _ c@Level{}     = return c



instance Substitutable Effect where
  type SubstitutionContext Effect x = MaybeT Checker x
  -- {TODO: Make effects richer}
  substitute subst e = return e

instance Substitutable CKind where
  type SubstitutionContext CKind x = x

  substitute subst (CPoly v) =
      case lookup v subst of
        Just (SubstCK k) -> k
        _                -> CPoly v
  substitute _ c@CConstr{} = c

instance Substitutable Kind where
  type SubstitutionContext Kind x = x

  substitute subst KType = KType
  substitute subst KCoeffect = KCoeffect
  substitute subst (KFun c1 c2) =
    KFun (substitute subst c1) (substitute subst c2)
  substitute subst (KPoly v) =
    case lookup v subst of
      Just (SubstK k) -> k
      _               -> KPoly v
  substitute subst (KConstr c) = KConstr c


{-| Take a context of 'a' and a subhstitution for 'a's (also a context)
  apply the substitution returning a pair of contexts, one for parts
  of the context where a substitution occurred, and one where substitution
  did not occur
>>> let ?globals = defaultGlobals in evalChecker initState (runMaybeT $ substCtxt [(mkId "y", TyInt 0)] [(mkId "x", Linear (TyVar $ mkId "x")), (mkId "y", Linear (TyVar $ mkId "y")), (mkId "z", Discharged (TyVar $ mkId "z") (CVar $ mkId "b"))])
Just ([(Id "y" "y",Linear (TyInt 0))],[(Id "x" "x",Linear (TyVar Id "x" "x")),(Id "z" "z",Discharged (TyVar Id "z" "z") (CVar Id "b" "b"))])
-}

substCtxt :: (?globals :: Globals) => Substitution -> Ctxt Assumption
  -> MaybeT Checker (Ctxt Assumption, Ctxt Assumption)
substCtxt _ [] = return ([], [])
substCtxt subst ((v, x):ctxt) = do
  (substituteds, unsubstituteds) <- substCtxt subst ctxt
  (v', x') <- substAssumption subst (v, x)
  if (v', x') == (v, x)
    then return (substituteds, (v, x) : unsubstituteds)
    else return ((v, x') : substituteds, unsubstituteds)


substAssumption :: (?globals :: Globals) => Substitution -> (Id, Assumption)
  -> MaybeT Checker (Id, Assumption)
substAssumption subst (v, Linear t) = do
    t <- substitute subst t
    return (v, Linear t)
substAssumption subst (v, Discharged t c) = do
    t <- substitute subst t
    c <- substitute subst c
    return (v, Discharged t c)

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


-- | Apply a name map to a type to rename the type variables
renameType :: (?globals :: Globals) => [(Id, Id)] -> Type -> MaybeT Checker Type
renameType subst t =
      typeFoldM (baseTypeFold { tfBox   = renameBox subst
                              , tfTyVar = renameTyVar subst }) t
  where
    renameBox renameMap c t = do
      c' <- substitute (map (\(v, var) -> (v, SubstC $ CVar var)) renameMap) c
      t' <- renameType renameMap t
      return $ Box c' t'
    renameTyVar renameMap v =
      case lookup v renameMap of
        Just v' -> return $ TyVar v'
        -- Shouldn't happen
        Nothing -> return $ TyVar v

-- | Get a fresh polymorphic instance of a type scheme and list of instantiated type variables
-- and their new names.
freshPolymorphicInstance :: (?globals :: Globals)
  => Quantifier -> TypeScheme -> MaybeT Checker (Type, [Id])
freshPolymorphicInstance quantifier (Forall s kinds ty) = do
    -- Universal becomes an existential (via freshCoeffeVar)
    -- since we are instantiating a polymorphic type
    renameMap <- mapM instantiateVariable kinds
    ty <- renameType renameMap ty
    return (ty, map snd renameMap)

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
               KType    -> error "Impossible" -- covered by typeBased
               KFun _ _ -> error "Tried to instantiate a non instantiatable kind"
      -- Return pair of old variable name and instantiated name (for
      -- name map)
      return (var, var')
    typeBased KType = True
    typeBased (KFun k1 k2) = typeBased k1 && typeBased k2
    typeBased _     = False
