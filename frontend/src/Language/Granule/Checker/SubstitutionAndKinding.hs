{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Granule.Checker.SubstitutionAndKinding(
  Substitutable(..),
  Unifiable(..),
  combineSubstitutions,
  combineManySubstitutions,
  freshPolymorphicInstance,
  synthKind,
  synthKindAssumption,
  checkKind,
  joinTypes,
  kindCheckDef,
  mguCoeffectTypesFromCoeffects,
  replaceSynonyms,
  updateTyVar,
  unify) where

import Control.Arrow (second)
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Data.Bifunctor.Foldable (bicataM)
import Data.Functor.Identity (runIdentity)
import Data.List (elemIndex, sortBy)
import Data.Maybe (fromMaybe, mapMaybe)

import Language.Granule.Context

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr hiding (Substitutable)
import Language.Granule.Syntax.Helpers hiding (freshIdentifierBase)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Checker.Effects (effectTop, effectUpperBound)
import Language.Granule.Checker.Flatten (mguCoeffectTypes, Injections)
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Primitives (closedOperation, coeffectResourceAlgebraOps, setElements, tyOps)
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Variables
--import Language.Granule.Checker.Normalise

import Language.Granule.Utils

class Substitutable t where
  -- | Rewrite a 't' using a substitution
  substitute :: (?globals :: Globals)
             => Substitution -> t -> Checker t

-- Instances for the main representation of things in the types

instance Substitutable Substitutors where

  substitute subst s =
    case s of
      SubstT t -> do
        t <- substitute subst t
        return $ SubstT t

      SubstK k -> do
        k <- substitute subst k
        return $ SubstK k

      SubstS sort -> do
        sort <- substitute subst sort
        return $ SubstS sort

-- Speciale case of substituting a substition
instance Substitutable Substitution where
  substitute subst [] = return []
  substitute subst ((var , s) : subst') = do
    s <- substitute subst s
    subst' <- substitute subst subst'
    case lookup var subst of
      Just (SubstT (TyVar var')) -> return $ (var', s) : subst'
      Nothing -> return subst'
      -- Shouldn't happen
      t -> error
        $ "Granule bug. Cannot rewrite a substitution `s` as the substitution map `s'` = "
        <> show subst <> " maps variable `" <> show var
        <> "` to a non variable type: `" <> show t <> "`"

instance Substitutable Type where
  substitute subst = typeFoldM (baseTypeFold
                              { tfTyVar = varSubst })
    where
      varSubst v = do
        case lookup v subst of
           Just (SubstT t) -> return t
           Just (SubstK t) -> return t
           _               -> mTyVar v

instance Substitutable t => Substitutable (Maybe t) where
  substitute s Nothing = return Nothing
  substitute s (Just t) = substitute s t >>= return . Just

combineManySubstitutions :: (?globals :: Globals)
    => Span -> [Substitution] -> Checker Substitution
combineManySubstitutions s [] = return []
combineManySubstitutions s (subst:ss) = do
  ss' <- combineManySubstitutions s ss
  combineSubstitutions s subst ss'

removeReflexivePairs :: Substitution -> Substitution
removeReflexivePairs [] = []
removeReflexivePairs ((v, SubstT (TyVar v')):subst) | v == v' = removeReflexivePairs subst
removeReflexivePairs ((v, SubstK (TyVar v')):subst) | v == v' = removeReflexivePairs subst
removeReflexivePairs ((v, e):subst) = (v, e) : removeReflexivePairs subst

-- | Combines substitutions which may fail if there are conflicting
-- | substitutions
combineSubstitutionsHere ::
    (?globals :: Globals)
    => Substitution -> Substitution -> Checker Substitution
combineSubstitutionsHere = combineSubstitutions nullSpan

-- | Combines substitutions which may fail if there are conflicting
-- | substitutions
combineSubstitutions ::
    (?globals :: Globals)
    => Span -> Substitution -> Substitution -> Checker Substitution
combineSubstitutions sp u1 u2 = do
      -- Remove any substitutions that say things like `a |-> a`. This leads to infite loops
      u1 <- return $ removeReflexivePairs u1
      u2 <- return $ removeReflexivePairs u2

      -- For all things in the (possibly empty) intersection of contexts `u1` and `u2`,
      -- check whether things can be unified, i.e. exactly
      uss1 <- forM u1 $ \(v, s) ->
        case lookupMany v u2 of
          -- Unifier in u1 but not in u2
          [] -> return [(v, s)]
          -- Possible unifications in each part
          alts -> do
              unifs <-
                forM alts $ \s' -> do
                   --(us, t) <- unifiable v t t' t t'
                   us <- unify s s'
                   case us of
                     Nothing -> throw UnificationFailGeneric { errLoc = sp, errSubst1 = s, errSubst2 = s' }
                     Just us -> do
                       sUnified <- substitute us s
                       combineSubstitutions sp [(v, sUnified)] us

              return $ concat unifs
      -- Any remaining unifiers that are in u2 but not u1
      uss2 <- forM u2 $ \(v, s) ->
         case lookup v u1 of
           Nothing -> return [(v, s)]
           _       -> return []
      let uss = concat uss1 <> concat uss2
      return $ reduceByTransitivity uss

reduceByTransitivity :: Substitution -> Substitution
reduceByTransitivity ctxt = reduceByTransitivity' [] ctxt
 where
   reduceByTransitivity' :: Substitution -> Substitution -> Substitution
   reduceByTransitivity' subst [] = subst

   reduceByTransitivity' substLeft (subst@(var, SubstT (TyVar var')):substRight) =
     case lookupAndCutout var' (substLeft ++ substRight) of
       Just (substRest, t) -> (var, t) : reduceByTransitivity ((var', t) : substRest)
       Nothing             -> reduceByTransitivity' (subst : substLeft) substRight

   reduceByTransitivity' substLeft (subst:substRight) =
     reduceByTransitivity' (subst:substLeft) substRight

{-| Take a context of 'a' and a subhstitution for 'a's (also a context)
  apply the substitution returning a pair of contexts, one for parts
  of the context where a substitution occurred, and one where substitution
  did not occur
>>> let ?globals = mempty in evalChecker initState (runMaybeT $ substCtxt [(mkId "y", SubstT $ TyInt 0)] [(mkId "x", Linear (TyVar $ mkId "x")), (mkId "y", Linear (TyVar $ mkId "y")), (mkId "z", Discharged (TyVar $ mkId "z") (TyVar $ mkId "b"))])
Just ([((Id "y" "y"),Linear (TyInt 0))],[((Id "x" "x"),Linear (TyVar (Id "x" "x"))),((Id "z" "z"),Discharged (TyVar (Id "z" "z")) (TyVar (Id "b" "b")))])
-}

instance Substitutable (Ctxt Assumption) where

  substitute subst ctxt = do
    (ctxt0, ctxt1) <- substCtxt subst ctxt
    let ctxtIds = getCtxtIds ctxt
    let combined = ctxt0 <> ctxt1
    -- Ensure that the resulting ctxt preserves the ordering of the input ctxt.
    return $ sortBy (\ (x, _) (y, _) -> elemIndex x ctxtIds `compare` elemIndex y ctxtIds) combined

substCtxt :: (?globals :: Globals) => Substitution -> Ctxt Assumption
  -> Checker (Ctxt Assumption, Ctxt Assumption)
substCtxt _ [] = return ([], [])
substCtxt subst ((v, x):ctxt) = do
  (substituteds, unsubstituteds) <- substCtxt subst ctxt
  (v', x') <- substAssumption subst (v, x)

  if (v', x') == (v, x)
    then return (substituteds, (v, x) : unsubstituteds)
    else return ((v, x') : substituteds, unsubstituteds)

substAssumption :: (?globals :: Globals) => Substitution -> (Id, Assumption)
  -> Checker (Id, Assumption)
substAssumption subst (v, Linear t) = do
    t <- substitute subst t
    return (v, Linear t)
substAssumption subst (v, Discharged t c) = do
    t <- substitute subst t
    c <- substitute subst c
    return (v, Discharged t c)

-- | Get a fresh polymorphic instance of a type scheme and list of instantiated type variables
-- and their new names.
freshPolymorphicInstance :: (?globals :: Globals)
  => Quantifier   -- ^ Variety of quantifier to resolve universals into (InstanceQ or BoundQ)
  -> Bool         -- ^ Flag on whether this is a data constructor-- if true, then be careful with existentials
  -> TypeScheme   -- ^ Type scheme to freshen
  -> Substitution -- ^ A substitution associated with this type scheme (e.g., for
                  --     data constructors of indexed types) that also needs freshening

  -> Checker (Type, Ctxt Kind, Substitution, [Type], Substitution)
    -- Returns the type (with new instance variables)
       -- a context of all the instance variables kinds (and the ids they replaced)
       -- a substitution from the visible instance variable to their originals
       -- a list of the (freshened) constraints for this scheme
       -- a correspondigly freshened version of the parameter substitution
freshPolymorphicInstance quantifier isDataConstructor (Forall s kinds constr ty) ixSubstitution = do
    -- Universal becomes an existential (via freshCoeffeVar)
    -- since we are instantiating a polymorphic type
    renameMap <- cumulativeMapM instantiateVariable kinds

    -- Applying the rename map to itself (one part at time), to accommodate dependency here
    renameMap <- selfRename renameMap

    -- Turn the rename map into a substitution
    let subst = ctxtMap (SubstT . TyVar . snd . fromEither) renameMap

    -- Freshen the types and constraints
    tyFreshened <- substitute subst ty
    constrFreshened <- mapM (substitute subst) constr

    -- Return the type and all instance variables
    let newTyVars = map (\(_, kv) -> swap . fromEither $ kv) renameMap
    let substLefts = ctxtMap (SubstT . TyVar . snd) $ justLefts renameMap

    ixSubstitution' <- substitute substLefts ixSubstitution

    return (tyFreshened, newTyVars, substLefts, constrFreshened, ixSubstitution')

  where
    -- Takes a renamep map and iteratively applies each renaming forwards to
    -- the rest of the rename map, substituting into kinds, and therefore
    -- implementing dependency between the type parameters
    selfRename [] = return []
    selfRename ((v, kv):xs) = do
      xs' <- mapM (substituteAlong [(v, SubstT . TyVar . snd . fromEither $ kv)]) xs
      xs'' <- selfRename xs'
      return $ (v, kv) : xs''

    substituteAlong subst (v, Left (k, v'))  = substitute subst k >>= (\k' -> return (v, Left (k', v')))
    substituteAlong subst (v, Right (k, v')) = substitute subst k >>= (\k' -> return (v, Right (k', v')))

    -- Freshen variables, create instance variables
    -- Left of id means a succesful instance variable created
    -- Right of id means that this is an existential and so an (externally visisble)
     --    instance variable is not generated
    instantiateVariable :: (Id, Kind) -> Checker (Id, Either (Kind, Id) (Kind, Id))
    instantiateVariable (var, k) =
      if isDataConstructor && (var `notElem` freeVars (resultType ty))
                           && (var `notElem` freeVars (ixSubstitution))
         then do
           -- Signals an existential
           var' <- freshTyVarInContextWithBinding var k ForallQ
           -- Don't return this as a fresh skolem variable
           return (var, Right (k, var'))

         else do

           var' <- freshTyVarInContextWithBinding var k quantifier
           return (var, Left (k, var'))

    -- Apply `f` but as we go apply the resulting substitution forwards on the rest of the list
    cumulativeMapM f [] = return []
    cumulativeMapM f (x:xs) = do
      eitherSubst1 <- f x
      -- Apply the substitution forwards on the list of kinds
      xs' <- mapM (\(v, k) -> substitute (ctxtMap (SubstT . TyVar . snd . fromEither) [eitherSubst1]) k
                               >>= (\k' -> return (v, k'))) xs
      substN <- cumulativeMapM f xs'
      return $ eitherSubst1 : substN

    fromEither :: Either a a -> a
    fromEither (Left a) = a
    fromEither (Right a) = a

    swap (a, b) = (b, a)

    -- Get just the lefts (used to extract just the skolems)
    justLefts = mapMaybe conv
      where conv (v, Left a)  = Just (v,  a)
            conv (v, Right _) = Nothing

instance Substitutable Pred where
  substitute ctxt =
      predFoldM
        (return . Conj)
        (return . Disj)
        (\idks p1 p2 -> do
             -- Apply substitution to id-kind pairs
             idks' <- mapM (\(id, k) -> substitute ctxt k >>= (\k -> return (id, k))) idks
             return $ Impl idks' p1 p2)
        -- Apply substitution also to the constraint
        (\c -> substitute ctxt c >>= (return . Con))
        (return . NegPred)
        -- Apply substitution also to the kinding
        (\id k p -> (substitute ctxt k) >>= (\k -> return $ Exists id k p))

instance Substitutable Constraint where
  substitute ctxt (Eq s c1 c2 k) = do
    c1 <- substitute ctxt c1
    c2 <- substitute ctxt c2
    k <- substitute ctxt k
    return $ Eq s c1 c2 k

  substitute ctxt (Neq s c1 c2 k) = do
    c1 <- substitute ctxt c1
    c2 <- substitute ctxt c2
    k <- substitute ctxt k
    return $ Neq s c1 c2 k

  substitute ctxt (Lub s c1 c2 c3 k) = do
    c1 <- substitute ctxt c1
    c2 <- substitute ctxt c2
    c3 <- substitute ctxt c3
    k <- substitute ctxt k
    return $ Lub s c1 c2 c3 k

  substitute ctxt (ApproximatedBy s c1 c2 k) = do
    c1 <- substitute ctxt c1
    c2 <- substitute ctxt c2
    k <- substitute ctxt k
    return $ ApproximatedBy s c1 c2 k

  substitute ctxt (Lt s c1 c2) = do
    c1 <- substitute ctxt c1
    c2 <- substitute ctxt c2
    return $ Lt s c1 c2

  substitute ctxt (Gt s c1 c2) = do
    c1 <- substitute ctxt c1
    c2 <- substitute ctxt c2
    return $ Gt s c1 c2

  substitute ctxt (LtEq s c1 c2) = LtEq s <$> substitute ctxt c1 <*> substitute ctxt c2
  substitute ctxt (GtEq s c1 c2) = GtEq s <$> substitute ctxt c1 <*> substitute ctxt c2

instance Substitutable (Equation () Type) where
  substitute ctxt (Equation sp name ty rf patterns expr) =
      do ty' <- substitute ctxt ty
         pat' <- mapM (substitute ctxt) patterns
         expr' <- substitute ctxt expr
         return $ Equation sp name ty' rf pat' expr'

substituteValue :: (?globals::Globals)
                => Substitution
                -> ValueF ev Type (Value ev Type) (Expr ev Type)
                -> Checker (Value ev Type)
substituteValue ctxt (AbsF ty arg mty expr) =
    do  ty' <- substitute ctxt ty
        arg' <- substitute ctxt arg
        mty' <- mapM (substitute ctxt) mty
        return $ Abs ty' arg' mty' expr
substituteValue ctxt (PromoteF ty expr) =
    do  ty' <- substitute ctxt ty
        return $ Promote ty' expr
substituteValue ctxt (PureF ty expr) =
    do  ty' <- substitute ctxt ty
        return $ Pure ty' expr
substituteValue ctxt (ConstrF ty ident vs) =
    do  ty' <- substitute ctxt ty
        return $ Constr ty' ident vs
substituteValue ctxt (ExtF ty ev) =
    do  ty' <- substitute ctxt ty
        return $ Ext ty' ev
substituteValue _ other = return (ExprFix2 other)

substituteExpr :: (?globals::Globals)
               => Substitution
               -> ExprF ev Type (Expr ev Type) (Value ev Type)
               -> Checker (Expr ev Type)
substituteExpr ctxt (AppF sp ty rf fn arg) =
    do  ty' <- substitute ctxt ty
        return $ App sp ty' rf fn arg
substituteExpr ctxt (AppTyF sp ty rf fn t) =
    do  ty' <- substitute ctxt ty
        t' <- substitute ctxt t
        return $ AppTy sp ty' rf fn t'
substituteExpr ctxt (BinopF sp ty rf op lhs rhs) =
    do  ty' <- substitute ctxt ty
        return $ Binop sp ty' rf op lhs rhs
substituteExpr ctxt (LetDiamondF sp ty rf pattern mty value expr) =
    do  ty' <- substitute ctxt ty
        pattern' <- substitute ctxt pattern
        mty' <- mapM (substitute ctxt) mty
        return $ LetDiamond sp ty' rf pattern' mty' value expr
substituteExpr ctxt (TryCatchF sp ty rf e1 pattern mty e2 e3) =
    do  ty' <- substitute ctxt ty
        pattern' <- substitute ctxt pattern
        mty' <- mapM (substitute ctxt) mty
        return $ TryCatch sp ty' rf e1 pattern' mty' e2 e3
substituteExpr ctxt (ValF sp ty rf value) =
    do  ty' <- substitute ctxt ty
        return $ Val sp ty' rf value
substituteExpr ctxt (CaseF sp ty rf expr arms) =
    do  ty' <- substitute ctxt ty
        arms' <- mapM (mapFstM (substitute ctxt)) arms
        return $ Case sp ty' rf expr arms'
substituteExpr ctxt (HoleF s a rf vs) = return $ Hole s a rf vs

mapFstM :: (Monad m) => (a -> m b) -> (a, c) -> m (b, c)
mapFstM fn (f, r) = do
    f' <- fn f
    return (f', r)

instance Substitutable (Expr () Type) where
  substitute ctxt = bicataM (substituteExpr ctxt) (substituteValue ctxt)

instance Substitutable (Value () Type) where
  substitute ctxt = bicataM (substituteValue ctxt) (substituteExpr ctxt)

instance Substitutable (Pattern Type) where
  substitute ctxt = patternFoldM
      (\sp ann rf nm -> do
          ann' <- substitute ctxt ann
          return $ PVar sp ann' rf nm)
      (\sp ann rf -> do
          ann' <- substitute ctxt ann
          return $ PWild sp ann' rf)
      (\sp ann rf pat -> do
          ann' <- substitute ctxt ann
          return $ PBox sp ann' rf pat)
      (\sp ann rf int -> do
          ann' <- substitute ctxt ann
          return $ PInt sp ann' rf int)
      (\sp ann rf doub -> do
          ann' <- substitute ctxt ann
          return $ PFloat sp ann' rf doub)
      (\sp ann rf nm pats -> do
          ann' <- substitute ctxt ann
          return $ PConstr sp ann' rf nm pats)

class Unifiable t where
    unify' :: (?globals :: Globals) => t -> t -> MaybeT Checker Substitution

unify :: (?globals :: Globals, Unifiable t) => t -> t -> Checker (Maybe Substitution)
unify x y = runMaybeT $ unify' x y

instance Unifiable Substitutors where
    unify' (SubstT t) (SubstT t') = unify' t t'
    unify' (SubstK k) (SubstK k') = unify' k k'
    unify' _ _ = fail ""

instance Unifiable Type where
    unify' t t' | t == t' = return []
    unify' (TyVar v) t    = return [(v, SubstT t)]
    unify' t (TyVar v)    = return [(v, SubstT t)]
    unify' (FunTy _ t1 t2) (FunTy _ t1' t2') = do
        u1 <- unify' t1 t1'
        u2 <- unify' t2 t2'
        lift $ combineSubstitutionsHere u1 u2
    unify' (Box c t) (Box c' t') = do
        u1 <- unify' c c'
        u2 <- unify' t t'
        lift $ combineSubstitutionsHere u1 u2
    unify' (Diamond e t) (Diamond e' t') = do
        u1 <- unify' e e'
        u2 <- unify' t t'
        lift $ combineSubstitutionsHere u1 u2
    unify' (TyApp t1 t2) (TyApp t1' t2') = do
        u1 <- unify' t1 t1'
        u2 <- unify' t2 t2'
        lift $ combineSubstitutionsHere u1 u2

    unify' t@(TyInfix o t1 t2) t'@(TyInfix o' t1' t2') = do
        (_, subst, k)   <- lift $ synthKind nullSpan t
        (_, subst', k') <- lift $ synthKind nullSpan t
        jK <- lift $ joinTypes nullSpan k k'
        case jK of
            Just (k, subst, _) -> do
              if o == o'
                then do
                  u1 <- unify' t1 t1'
                  u2 <- unify' t2 t2'
                  u  <- lift $ combineSubstitutionsHere u1 u2
                  u' <- lift $ combineSubstitutionsHere u subst
                  lift $ combineSubstitutionsHere u' subst'
                else do
                  lift $ addConstraint $ Eq nullSpan t t' k
                  return subst

            -- No unification
            _ -> fail ""

    unify' (TyCase t branches) (TyCase t' branches') = do
      u <- unify' t t'
      let branches1 = sortBy (\x y -> compare (fst x) (fst y)) branches
      let branches2 = sortBy (\x y -> compare (fst x) (fst y)) branches'
      if map fst branches1 == map fst branches2
        then do
          us <- zipWithM unify' (map snd branches1) (map snd branches2)
          lift $ combineManySubstitutions nullSpan (u : us)
        else
          -- patterns are different in a case
          fail ""

    unify' (TySig t k) (TySig t' k') = do
      u  <- unify' t t'
      u' <- unify' k k'
      lift $ combineSubstitutionsHere u u'

    -- No unification
    unify' _ _ = fail ""

instance Unifiable t => Unifiable (Maybe t) where
    unify' Nothing _ = return []
    unify' _ Nothing = return []
    unify' (Just x) (Just y) = unify' x y

updateTyVar :: (?globals :: Globals) => Span -> Id -> Kind -> Checker ()
updateTyVar s tyVar k = do
    -- Updated the kind of type variable `v` in the context
    st <- get
    -- Get the current quantification
    case lookup tyVar (tyVarContext st) of
      Just (_, q) -> do
          modify (\st -> st{ tyVarContext = rewriteCtxt (tyVarContext st) })
          -- Rewrite the predicate

          st <- get
          let subst = [(tyVar, SubstK k)]
          ps <- mapM (substitute subst) (predicateStack st)
          put st{ predicateStack = ps }

      Nothing -> throw UnboundVariableError{ errLoc = s, errId = tyVar }
  where
    rewriteCtxt :: Ctxt (Type, Quantifier) -> Ctxt (Type, Quantifier)
    rewriteCtxt [] = []
    rewriteCtxt ((name, (TyVar kindVar, q)) : ctxt)
     | tyVar == kindVar = (name, (k, q)) : rewriteCtxt ctxt
    rewriteCtxt ((name, (TyVar kindVar, q)) : ctxt)
     | tyVar == kindVar = (name, (k, q)) : rewriteCtxt ctxt
    rewriteCtxt (x : ctxt) = x : rewriteCtxt ctxt

--------------------------------------------------------------------------------
-- Below this point is the KindsAlgorithmic module, moved here to temporarily --
-- get around cyclic module dependencies.                                     --
--------------------------------------------------------------------------------

-- module Language.Granule.Checker.KindsAlgorithmic where

-- | Check the kind of a definition
-- Currently we expec t that a type scheme has kind ktype
kindCheckDef :: (?globals :: Globals) => Def v t -> Checker (Def v t)
kindCheckDef (Def s id rf eqs (Forall s' quantifiedVariables constraints ty)) = do
  let localTyVarContext = universify quantifiedVariables

  -- Set up the quantified variables in the type variable context
  modify (\st -> st { tyVarContext = localTyVarContext })
  forM_ constraints $ \constraint -> checkKind s constraint kpredicate

  ty <- return $ replaceSynonyms ty
  (unifiers, tyElaborated) <- checkKind s ty ktype

  -- Rewrite the quantified variables with their possibly updated kinds (inferred)
  qVars <- mapM (\(v, a) -> substitute unifiers a >>= (\b -> return (v, b))) quantifiedVariables
  modify (\st -> st { tyVarContext = [] })

  -- Update the def with the resolved quantifications
  return (Def s id rf eqs (Forall s' qVars constraints tyElaborated))

-- Replace any constructor IDs with their top-element
-- (i.e., IO gets replaces with the set of all effects as an alias)
replaceSynonyms :: Type -> Type
replaceSynonyms = runIdentity . typeFoldM (baseTypeFold { tfTyCon = conCase })
  where
    conCase conId = let tyConId = TyCon conId in return $ fromMaybe tyConId (effectTop tyConId)

-- `checkKind s gam t k` checks with `gam |- t :: k` is derivable
-- and also returns an elaborated type term `t'` in the case that
-- some extra information is learned (e.g., resolving types of coeffect terms)
checkKind :: (?globals :: Globals) =>
  Span -> Type -> Kind -> Checker (Substitution, Type)

-- KChk_funk
checkKind s (FunTy name t1 t2) k = do
  (subst1, t1') <- checkKind s t1 k
  (subst2, t2') <- checkKind s t2 k
  substFinal <- combineSubstitutions s subst1 subst2
  return (substFinal, FunTy name t1 t2)

-- KChk_app
checkKind s (TyApp t1 t2) k2 = do
  (k1, subst1, t2') <- synthKind s t2
  (subst2, t1') <- checkKind s t1 (FunTy Nothing k1 k2)
  substFinal <- combineSubstitutions s subst1 subst2
  return (substFinal, TyApp t1' t2')

-- KChk_opRing and KChk_effOp combined (i.e. closed operators)
checkKind s t@(TyInfix op t1 t2) k | closedOperation op = do
  maybeSubst <- closedOperatorAtKind s op k
  case maybeSubst of
    Just subst3 -> do
      (subst1, t1') <- checkKind s t1 k
      (subst2, t2') <- checkKind s t2 k
      substFinal <- combineManySubstitutions s [subst1, subst2, subst3]
      return (substFinal, TyInfix op t1' t2')
    Nothing -> throw OperatorUndefinedForKind { errLoc = s, errTyOp = op, errK = k }

-- KChk_nat
checkKind s t@(TyInt n) k =
  case k of
    -- n : Nat
    TyCon (internalName -> "Nat") -> return ([], t)
    -- n : Q
    TyCon (internalName -> "Q") -> return ([], t)
    -- n : Ext Nat
    TyApp (TyCon (internalName -> "Ext")) (TyCon (internalName -> "Nat")) -> return ([], t)
    -- n : Interval k  (then we turn this into [n..n])
    TyApp (TyCon (internalName -> "Interval")) k' -> do
      (subst, k'') <- checkKind s t k'
      return (subst, TyInfix TyOpInterval t t)
    -- Not valid
    _ -> throw $ NaturalNumberAtWrongKind s t k

-- KChk_effOne
checkKind s t@(TyGrade mk n) k = do
  let k' = fromMaybe k mk
  jK <- maybe (return (Just (k, [], Nothing))) (\k' -> joinTypes s k' k) mk
  case jK of
    Just (k, subst, _) ->
      case n of
        0 -> do -- Can only be a semiring element
          (subst', _) <- checkKind s k kcoeffect
          substFinal <- combineSubstitutions s subst subst'
          return (substFinal, TyGrade (Just k) n)
        1 -> do -- Can be a monoid or semiring element
          (subst', _) <- (checkKind s k kcoeffect) <|> (checkKind s k keffect)
          substFinal <- combineSubstitutions s subst subst'
          return (substFinal, TyGrade (Just k) n)
        _ -> do -- Can only be a semiring element formed by repeated 1 + ...
          (subst', _) <- checkKind s k kcoeffect
          substFinal <- combineSubstitutions s subst subst'
          return (substFinal, TyGrade (Just k) n)
    Nothing ->
      throw $ UnificationError s k k'

-- KChk_sig
checkKind s (TySig t k) k' = do
  join <- joinTypes s k k'
  case join of
    Just (jk, subst, inj) ->
      case inj of
        Nothing           -> return (subst, TySig t jk)
        -- Apply the left injection
        Just (inj1, inj2) -> return (subst, TySig (inj1 t) jk)
    Nothing -> throw KindMismatch { errLoc = s, tyActualK = Just t, kExpected = k, kActual = k' }

-- KChck_Nat
-- "Nat" belonds to Coeffect, Effect, and Type kinds
checkKind s t@(TyCon (internalName -> "Nat")) (TyCon (internalName -> "Coeffect")) =
  return ([], t)
checkKind s t@(TyCon (internalName -> "Nat")) (TyCon (internalName -> "Effect")) =
  return ([], t)
checkKind s t@(TyCon (internalName -> "Nat")) (Type 0) =
  return ([], t)

-- Fall through to synthesis if checking can not be done.
checkKind s t k = do
  (k', subst1, t') <- synthKind s t
  join <- joinTypes s k k'
  case join of
    Just (_, subst2, _) -> do
      substFinal <- combineSubstitutions s subst1 subst2
      return (substFinal, t')
    Nothing -> throw KindMismatch { errLoc = s, tyActualK = Just t, kExpected = k, kActual = k' }

-- Given `synthKind gam t` it synthesis a `k` such that `gam |- t :: k` and
-- returns a substitution and an elebaroted type `t'` along with it.
synthKind :: (?globals :: Globals) =>
  Span -> Type -> Checker (Kind, Substitution, Type)
synthKind s t = synthKind' s (not (containsTypeSig t)) t

synthKind' :: (?globals :: Globals) =>
     Span
  -> Bool  -- Special flag: True means we can treat TyGrade as a Nat because there are no signatures
  -> Type
  -> Checker (Kind, Substitution, Type)

-- KChkS_var and KChkS_instVar
synthKind' s overloadToNat t@(TyVar x) = do
  st <- get
  case lookup x (tyVarContext st) of
    Just (k, _) -> return (k, [], t)
    Nothing     -> throw UnboundTypeVariable { errLoc = s, errId = x }


-- -- KChkS_fun
--
--      t1 => k    t2 <= k
--   ----------------------- Fun
--        t1 -> t2 => k

synthKind' s overloadToNat (FunTy name t1 t2) = do
  (k, subst1, t1') <- synthKind' s overloadToNat t1
  (subst2   , t2') <- checkKind s t2 k
  subst <- combineSubstitutions s subst1 subst2
  return (k, subst, FunTy name t1' t2')

-- KChkS_pair
synthKind' s overloadToNat (TyApp (TyApp (TyCon (internalName -> ",,")) t1) t2) = do
  (k1, subst1, t1') <- synthKind' s overloadToNat t1
  (k2, subst2, t2') <- synthKind' s overloadToNat t2
  subst <- combineSubstitutions s subst1 subst2
  return (TyApp (TyApp (TyCon $ mkId ",,") k1) k2, subst, TyApp (TyApp (TyCon $ mkId ",,") t1') t2')

-- KChkS_app
--
--      t1 => k1 -> k2    t2 <= k1
--   ------------------------------ Fun
--        t1 t2 => k
--
synthKind' s overloadToNat (TyApp t1 t2) = do
  debugM "synthKind" (pretty (TyApp t1 t2))
  (funK, subst1, t1') <- synthKind' s overloadToNat t1
  debugM "synthKind t1 kind" (show funK)
  case funK of
    (FunTy _ k1 k2) -> do
      (subst2, t2') <- checkKind s t2 k1
      subst <- combineSubstitutions s subst1 subst2
      return (k2, subst, TyApp t1' t2')
    _ -> throw KindError { errLoc = s, errTy = t1, errKL = funK }

-- KChkS_interval
--
--      t1 => k1        t2 => k2     k1 ~ k2 =  k3
--   ----------------------------------------------- interval
--        t1 .. t2 => Interval k3
--
synthKind' s overloadToNat (TyInfix TyOpInterval t1 t2) = do
  (coeffTy1, subst1, t1') <- synthKind' s overloadToNat t1
  (coeffTy2, subst2, t2') <- synthKind' s overloadToNat t2
  (jcoeffTy, subst3, (inj1, inj2)) <- mguCoeffectTypes s coeffTy1 coeffTy2
  subst <- combineManySubstitutions s [subst1, subst2, subst3]
  -- Apply injections in the elaborated term
  return (TyApp (tyCon "Interval") jcoeffTy, subst, TyInfix TyOpInterval (inj1 t1') (inj2 t2'))

-- KChkS_predOp
synthKind' s overloadToNat t@(TyInfix op t1 t2) =
  synthForOperator s overloadToNat op t1 t2

-- KChkS_int
synthKind' s _ t@(TyInt n) = do
  return (TyCon (Id "Nat" "Nat"), [], t)

-- KChkS_grade [overload to Nat]
synthKind' s overloadToNat t@(TyGrade Nothing n) | overloadToNat =
  return (tyCon "Nat", [], TyInt n)

-- KChkS_grade [don't overload to Nat]
synthKind' s overloadToNat t@(TyGrade (Just k) n) =
  return (k, [], t)

-- KChkS_grade [don't overload to Nat]
synthKind' s overloadToNat t@(TyGrade Nothing n) | not overloadToNat = do
  -- TODO: is it problematic that we choose a semiring (coeffect)-kinded type
  -- rather than an effect one?
  var <- freshTyVarInContext (mkId $ "semiring[" <> pretty (startPos s) <> "]") kcoeffect
  return (TyVar var, [], t)

-- KChkS_box
synthKind' s _ (Box c t) = do
  -- Deal with the grade term
  (coeffTy, subst0, c') <- synthKind' s (not (containsTypeSig c)) c
  (subst1, _) <- checkKind s coeffTy kcoeffect
  -- Then the inner type
  (subst2, t') <- checkKind s t ktype
  subst <- combineManySubstitutions s [subst0, subst1, subst2]
  return (ktype, subst, Box c' t')

-- KChkS_dia
synthKind' s _ (Diamond e t) = do
  (innerK, subst2, e') <- synthKind s e
  (subst1, _)  <- checkKind s innerK keffect
  (subst3, t') <- checkKind s t ktype
  subst <- combineManySubstitutions s [subst1, subst2, subst3]
  return (ktype, subst, Diamond e' t')

synthKind' s _ t@(TyCon (internalName -> "Pure")) = do
  -- Create a fresh type variable
  var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") keffect
  return (TyVar var, [], t)

synthKind' s _ t@(TyCon (internalName -> "Handled")) = do
  var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") keffect
  return $ ((FunTy Nothing (TyVar var) (TyVar var)), [], t)

-- KChkS_con
synthKind' s _ t@(TyCon id) = do
  st <- get
  case lookup id (typeConstructors st)  of
    Just (kind', _, _) -> return (kind', [], t)
    Nothing -> do
      mConstructor <- lookupDataConstructor s id
      case mConstructor of
        Just (Forall _ [] [] tDat, _) -> return (tDat, [], t)
        Just _ -> error $ pretty s <> "I'm afraid I can't yet promote the polymorphic data constructor:"  <> pretty id
        Nothing -> throw UnboundTypeConstructor { errLoc = s, errId = id }

-- KChkS_set
synthKind' s overloadToNat t0@(TySet (t:ts)) = do
  (k, subst1, t') <- synthKind' s overloadToNat t
  substsAndTs' <- mapM (\t' -> checkKind s t' k) ts
  let (substs, ts') = unzip substsAndTs'
  subst <- combineManySubstitutions s (subst1:substs)
  case lookup k setElements of
    -- Lift this alias to the kind level
    Just t  -> return (t, subst, TySet (t':ts'))
    Nothing -> return (TyApp (TyCon $ mkId "Set") k, subst, TySet (t':ts'))

-- KChkS_sig
synthKind' s _ (TySig t k) = do
  (subst, t') <- checkKind s t k
  return (k, subst, TySig t' k)

synthKind' s _ t =
  throw ImpossibleKindSynthesis { errLoc = s, errTy = t }

synthForOperator :: (?globals :: Globals)
  => Span
  -> Bool -- flag whether overloading to Nat is allowed
  -> TypeOperator
  -> Type
  -> Type
  -> Checker (Kind, Substitution, Type)
synthForOperator s overloadToNat op t1 t2 = do
  debugM "synthForOperator" ("ov = " ++ show overloadToNat ++ "op = " ++ pretty op ++ " is closed = " ++ show (closedOperation op))
  if predicateOperation op || closedOperation op
    then do
      debugM "t1" (show t1)
      (k1, subst1, t1') <- synthKind' s overloadToNat t1
      debugM "synthForOperator" ("k1 = " ++ pretty k1)
      (k2, subst2, t2') <- synthKind' s overloadToNat t2
      debugM "synthForOperator" ("k2 = " ++ pretty k2)

      (k3, substK, (inj1, inj2)) <- mguCoeffectTypes s k1 k2
      debugM "synthForOperator" ("unif k1 k2 = " ++ pretty k3)


      maybeSubst <- if predicateOperation op
                      then predicateOperatorAtKind s op k3
                      else closedOperatorAtKind s op k3
      case maybeSubst of
        Just subst3 -> do
          subst <- combineManySubstitutions s [subst1, subst2, subst3, substK]
          if predicateOperation op
            then return (kpredicate, subst, TyInfix op (inj1 t1') (inj2 t2'))
            else return (k3, subst, TyInfix op (inj1 t1') (inj2 t2'))

        Nothing -> throw OperatorUndefinedForKind { errLoc = s, errTyOp = op, errK = k1 }
    else throw ImpossibleKindSynthesis { errLoc = s, errTy = TyInfix op t1 t2 }

-- | `closedOperatorAtKind` takes an operator `op` and a kind `k` and returns a
-- substitution if this is a valid operator at kind `k -> k -> k`.
closedOperatorAtKind :: (?globals :: Globals)
  => Span
  -> TypeOperator
  -> Kind
  -> Checker (Maybe Substitution)

-- Nat case
closedOperatorAtKind _ op (TyCon (internalName -> "Nat")) =
  return $ if closedOperation op then Just [] else Nothing

-- Expontentiation on effects also allowed
closedOperatorAtKind s TyOpExpon t = do
  _ <- checkKind s t keffect
  return $ Just []

-- * case
closedOperatorAtKind s TyOpTimes t = do
  -- See if the type is a coeffect
  (result, putChecker) <- peekChecker (checkKind s t kcoeffect)
  case result of
    Left _ -> do
      -- If not, see if the type is an effect
      (result', putChecker') <- peekChecker (checkKind s t keffect)
      case result' of
        -- Not a closed operator at this kind
        Left  _ -> return Nothing
        -- Yes it is an effect type
        Right (subst, _) -> do
          putChecker'
          return $ Just subst
    -- Yes it is a coeffect type
    Right (subst, _) -> do
      putChecker
      return $ Just subst

-- Any other "coeffect operators" case
closedOperatorAtKind s op t | coeffectResourceAlgebraOps op = do
  -- See if the type is a coeffect
  (result, putChecker) <- peekChecker (checkKind s t kcoeffect)
  case result of
    Left _ -> return Nothing
    Right (subst, _) -> do
      putChecker
      return $ Just subst
      --return $ Just (FunTy t (FunTy t t, subst))

closedOperatorAtKind _ op (TyVar _) =
  return $ if closedOperation op then Just [] else Nothing

closedOperatorAtKind _ _ _ = return Nothing

-- | `predicateOperatorAtKind` takes an operator `op` and a kind `k` and returns
-- a substitution if this is a valid operator at kind `k -> k -> kpredicate`.
predicateOperatorAtKind :: (?globals :: Globals) =>
  Span -> TypeOperator -> Kind -> Checker (Maybe Substitution)
predicateOperatorAtKind s op t | predicateOperation op = do
  (result, putChecker) <- peekChecker (checkKind s t kcoeffect)
  case result of
    Left _ -> return Nothing
    Right (subst, _) -> do
      putChecker
      return $ Just subst
predicateOperatorAtKind s op k@(TyVar _) =
    return $ if predicateOperation op then Just [] else Nothing
predicateOperatorAtKind _ _ _ = return Nothing

-- | Determines if a type operator produces results of kind kpredicate.
predicateOperation :: TypeOperator -> Bool
predicateOperation op = (\(_, _, c) -> c) (tyOps op) == kpredicate

-- | Compute the join of two types, if it exists
-- | (including injections in the case of coeffect types)

joinTypes :: (?globals :: Globals)
          => Span
          -> Type
          -> Type
          -> Checker (Maybe (Type, Substitution, Maybe Injections))
joinTypes s t1 t2 = runMaybeT (joinTypes' s t1 t2)

joinTypes' :: (?globals :: Globals)
          => Span
          -> Type
          -> Type
          -> MaybeT Checker (Type, Substitution, Maybe Injections)
joinTypes' s t t' | t == t' = return (t, [], Nothing)

joinTypes' s (FunTy id t1 t2) (FunTy _ t1' t2') = do
  (t1j, subst1, _) <- joinTypes' s t1' t1 -- contravariance
  (t2j, subst2, _) <- joinTypes' s t2 t2'
  subst <- lift $ combineSubstitutions s subst1 subst2
  return (FunTy id t1j t2j, subst, Nothing)

joinTypes' s (Diamond ef1 t1) (Diamond ef2 t2) = do
  (tj, subst0, _) <- joinTypes' s t1 t2
  -- Calculate the effect type for the effects here
  (efty1, subst1, ef1') <- lift $ synthKind s ef1
  (efty2, subst2, ef2') <- lift $ synthKind s ef2
  -- Compute the upper bound on the types
  (efftj, subst3, _) <- joinTypes' s efty1 efty2
  -- Computes the upper bound on the effects
  ej <- lift $ effectUpperBound s efftj ef1' ef2'
  subst <- lift $ combineManySubstitutions s [subst0, subst1, subst2, subst3]
  return (Diamond ej tj, subst, Nothing)

joinTypes' s (Box c t) (Box c' t') = do
  (coeffTy, subst, (inj1, inj2)) <- lift $ mguCoeffectTypesFromCoeffects s c c'
  -- Create a fresh coeffect variable
  topVar <- lift $ freshTyVarInContext (mkId "") coeffTy
  -- Unify the two coeffects into one
  lift $ addConstraint (ApproximatedBy s (inj1 c)  (TyVar topVar) coeffTy)
  lift $ addConstraint (ApproximatedBy s (inj2 c') (TyVar topVar) coeffTy)
  (tUpper, subst', _) <- joinTypes' s t t'
  substFinal <- lift $ combineSubstitutions s subst subst'
  return (Box (TyVar topVar) tUpper, substFinal, Nothing)

-- -- TODO: Replace how this Nat is constructed?
-- OLD APPROACH- WHICH IS A BIT WEIRD... but something in it?
-- joinTypes s (TyInt n) (TyVar m) = do
--     -- Create a fresh coeffect variable
--   let ty = TyCon $ mkId "Nat"
--   var <- freshTyVarInContext m ty
--   -- Unify the two coeffects into one
--   addConstraint (Eq s (TyInt n) (TyVar var) ty)
--   return $ TyInt n

joinTypes' _ (TyVar v) t = do
  st <- get
  case lookup v (tyVarContext st) of
    Just (_, q) | q == InstanceQ || q == BoundQ -> return (t, [(v, SubstT t)], Nothing)
    -- Occurs if an implicitly quantified variable has arisen
    Nothing -> return (t, [(v, SubstT t)], Nothing)
    -- Don't unify with universal variables
    _ -> fail "Cannot unify with a universal"

joinTypes' s t1 t2@(TyVar _) = joinTypes' s t2 t1

joinTypes' s (TyApp t1 t2) (TyApp t1' t2') = do
  (t1'', subst1, _) <- joinTypes' s t1 t1'
  (t2'', subst2, _) <- joinTypes' s t2 t2'
  subst <- lift $ combineSubstitutions s subst1 subst2
  return (TyApp t1'' t2'', subst, Nothing)

joinTypes' s t1 t2 = do
  st <- get
  (isCoeffect1, putChecker1) <- lift $ attemptChecker (checkKind s t1 kcoeffect)
  (isCoeffect2, putChecker2) <- lift $ attemptChecker (checkKind s t2 kcoeffect)
  -- Case where the two types are actually coeffect types
  if isCoeffect1 && isCoeffect2
    then lift $ do
      -- Find the most general unifier for the types
      putChecker1
      putChecker2
      (jcoeffTy, subst, injections) <- mguCoeffectTypes s t1 t2
      return (jcoeffTy, subst, Just injections)
    else
      -- Fall through
      fail "No upper bound"

-- Universally quantifies everything in a context.
universify :: Ctxt Kind -> Ctxt (Type, Quantifier)
universify = map (second (\k -> (k, ForallQ)))

synthKindAssumption :: (?globals :: Globals) => Span -> Assumption -> Checker (Maybe Type, Substitution)
synthKindAssumption _ (Linear _) = return (Nothing, [])
synthKindAssumption s (Discharged _ c) = do
  (t, subst, _) <- synthKind s c
  return (Just t, subst)

-- Find the most general unifier of two coeffects
-- This is an effectful operation which can update the coeffect-kind
-- contexts if a unification resolves a variable
mguCoeffectTypesFromCoeffects :: (?globals :: Globals)
  => Span
  -> Type
  -> Type
  -> Checker (Type, Substitution, (Type -> Type, Type -> Type))
mguCoeffectTypesFromCoeffects s c1 c2 = do
  debugM "mguCoeffectTypesFromCoeffects" (show c1 <> ", " <> show c2)
  (coeffTy1, subst1, _) <- synthKind s c1
  debugM "coeffTy1 = " (pretty coeffTy1)
  (coeffTy2, subst2, _) <- synthKind s c2
  debugM "coeffTy2 = " (pretty coeffTy2)
  (coeffTy, subst3, res) <- mguCoeffectTypes s coeffTy1 coeffTy2
  subst <- combineManySubstitutions s [subst1, subst2, subst3]
  return (coeffTy, subst, res)
