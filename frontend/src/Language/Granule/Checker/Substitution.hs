{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Granule.Checker.Substitution where

import Control.Arrow (second)
import Control.Monad
import Control.Monad.Except (catchError)
import Control.Monad.State.Strict
import Data.Bifunctor.Foldable (bicataM)
import Data.Foldable (foldrM)
import Data.Functor.Identity (runIdentity)
import Data.List (elemIndex, sortBy)
import Data.Maybe (mapMaybe)

import Language.Granule.Context

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr hiding (Substitutable)
import Language.Granule.Syntax.Helpers hiding (freshIdentifierBase)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Checker.Constraints.CompileNatKinded
import Language.Granule.Checker.Effects (effectTop)
import Language.Granule.Checker.Flatten (mguCoeffectTypes)
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Primitives (closedOperation, coeffectResourceAlgebraOps, setElements, tyOps)
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Variables

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

      SubstC c -> do
        c <- substitute subst c
        return $ SubstC c

      SubstK k -> do
        k <- substitute subst k
        return $ SubstK k

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
                              { tfTyVar = varSubst
                              , tfBox = box
                              , tfDiamond = dia })
    where
      box c t = do
        c <- substitute subst c
        mBox c t

      dia e t = do
        e <- substitute subst e
        mDiamond e t

      varSubst v =
         case lookup v subst of
           Just (SubstT t) -> return t
           _               -> mTyVar v

instance Substitutable Coeffect where

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

    substitute subst (CMinus c1 c2) = do
        c1' <- substitute subst c1
        c2' <- substitute subst c2
        return $ CMinus c1' c2'

    substitute subst (CExpon c1 c2) = do
        c1' <- substitute subst c1
        c2' <- substitute subst c2
        return $ CExpon c1' c2'

    substitute subst (CInterval c1 c2) = do
        c1' <- substitute subst c1
        c2' <- substitute subst c2
        return $ CInterval c1' c2'

    substitute subst (CProduct c1 c2) = do
        c1' <- substitute subst c1
        c2' <- substitute subst c2
        return $ CProduct c1' c2'

    substitute subst (CVar v) =
        case lookup v subst of
            Just (SubstC c) -> do
                checkerState <- get
                case lookup v (tyVarContext checkerState) of
                    -- If the coeffect variable has a poly kind then update it with the
                    -- kind of c
                    Just ((KVar kv), q) -> do
                        (coeffTy, _) <- inferCoeffectType nullSpan c
                        put $ checkerState { tyVarContext = replace (tyVarContext checkerState)
                                                                    v (promoteTypeToKind coeffTy, q) }

                    _ -> return ()
                return c

            -- Substitution of a ty var becomes a coeffect var
            Just (SubstT (TyVar v')) ->
              return $ CVar v'

            -- Substitution of a type (that is not just a variable) can
            -- be done if we convert the type term into a coeffect term
            -- NOTE: This will go away when we merge the Coeffect syntax just into Type
            Just (SubstT t) -> do
                st <- get
                (k, _) <- synthKind nullSpan (tyVarContext st) t
                (k', _) <- inferCoeffectType nullSpan (CVar v)
                jK <- joinKind k (promoteTypeToKind k')
                case jK of
                    Just (KPromote (TyCon (internalName -> "Nat")), _) ->
                        compileNatKindedTypeToCoeffect nullSpan t
                    _ -> return (CVar v)

            _  -> return $ CVar v

    substitute subst (CInfinity k) = do
        k <- substitute subst k
        return $ CInfinity k

    substitute subst (COne k) = do
        k <- substitute subst k
        return $ COne k

    substitute subst (CZero k) = do
        k <- substitute subst k
        return $ CZero k

    substitute subst (CSet tys) = do
        tys <- mapM (\(v, t) -> substitute subst t >>= (\t' -> return (v, t'))) tys
        return $ CSet tys

    substitute subst (CSig c k) = do
        c <- substitute subst c
        k <- substitute subst k
        return $ CSig c k

    substitute _ c@CNat{}      = return c
    substitute _ c@CFloat{}    = return c
    substitute _ c@Level{}     = return c

instance Substitutable Kind where

  substitute subst (KPromote t) = do
      t <- substitute subst t
      return $ KPromote t

  substitute subst KType = return KType
  substitute subst KEffect = return KEffect
  substitute subst KCoeffect = return KCoeffect
  substitute subst KPredicate = return KPredicate
  substitute subst (KFun c1 c2) = do
    c1 <- substitute subst c1
    c2 <- substitute subst c2
    return $ KFun c1 c2
  substitute subst (KVar v) =
    case lookup v subst of
      Just (SubstK k) -> return k
      Just (SubstT t) -> return $ KPromote t
      _               -> return $ KVar v
  substitute subst (KUnion k1 k2) = do
    k1' <- substitute subst k1
    k2' <- substitute subst k2
    return $ KUnion k1' k2'

instance Substitutable t => Substitutable (Maybe t) where
  substitute s Nothing = return Nothing
  substitute s (Just t) = substitute s t >>= return . Just

-- | Combine substitutions wrapped in Maybe
(<<>>) :: (?globals :: Globals)
  => Maybe Substitution -> Maybe Substitution -> Checker (Maybe Substitution)
xs <<>> ys =
  case (xs, ys) of
    (Just xs', Just ys') ->
         combineSubstitutions nullSpan xs' ys' >>= (return . Just)
    _ -> return Nothing

combineManySubstitutions :: (?globals :: Globals)
    => Span -> [Substitution] -> Checker Substitution
combineManySubstitutions s [] = return []
combineManySubstitutions s (subst:ss) = do
  ss' <- combineManySubstitutions s ss
  combineSubstitutions s subst ss'

removeReflexivePairs :: Substitution -> Substitution
removeReflexivePairs [] = []
removeReflexivePairs ((v, SubstT (TyVar v')):subst) | v == v' = removeReflexivePairs subst
removeReflexivePairs ((v, SubstC (CVar v')):subst) | v == v' = removeReflexivePairs subst
removeReflexivePairs ((v, SubstK (KVar v')):subst) | v == v' = removeReflexivePairs subst
removeReflexivePairs ((v, e):subst) = (v, e) : removeReflexivePairs subst

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
>>> let ?globals = mempty in evalChecker initState (runMaybeT $ substCtxt [(mkId "y", SubstT $ TyInt 0)] [(mkId "x", Linear (TyVar $ mkId "x")), (mkId "y", Linear (TyVar $ mkId "y")), (mkId "z", Discharged (TyVar $ mkId "z") (CVar $ mkId "b"))])
Just ([((Id "y" "y"),Linear (TyInt 0))],[((Id "x" "x"),Linear (TyVar (Id "x" "x"))),((Id "z" "z"),Discharged (TyVar (Id "z" "z")) (CVar (Id "b" "b")))])
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
        (\ids p1 p2 -> return $ Impl ids p1 p2)
        (\c -> substitute ctxt c >>= return . Con)
        (return . NegPred)
        (\ids k p -> substitute ctxt k >>= \k' -> return $ Exists ids k' p)

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

  substitute ctxt (NonZeroPromotableTo s v c k) = do
    c <- substitute ctxt c
    k <- substitute ctxt k
    return $ NonZeroPromotableTo s v c k

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
  substitute ctxt (Equation sp ty rf patterns expr) =
      do ty' <- substitute ctxt ty
         pat' <- mapM (substitute ctxt) patterns
         expr' <- substitute ctxt expr
         return $ Equation sp ty' rf pat' expr'

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
substituteExpr ctxt (BinopF sp ty rf op lhs rhs) =
    do  ty' <- substitute ctxt ty
        return $ Binop sp ty' rf op lhs rhs
substituteExpr ctxt (LetDiamondF sp ty rf pattern mty value expr) =
    do  ty' <- substitute ctxt ty
        pattern' <- substitute ctxt pattern
        mty' <- mapM (substitute ctxt) mty
        return $ LetDiamond sp ty' rf pattern' mty' value expr
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
    unify :: (?globals :: Globals) => t -> t -> Checker (Maybe Substitution)

instance Unifiable Substitutors where
    unify (SubstT t) (SubstT t') = unify t t'
    unify (SubstT t) (SubstC c') = do
        st <- get
        -- We can unify a type with a coeffect, if the type is actually a Nat
        (k, _) <- synthKind nullSpan (tyVarContext st) t
        (k', subst) <- inferCoeffectType nullSpan c'
        jK <- joinKind k (KPromote k')
        case jK of
            Just (KPromote (TyCon k), _) | internalName k == "Nat" -> do
                c <- compileNatKindedTypeToCoeffect nullSpan t
                substM <- unify c c'
                case substM of
                  Nothing -> return $ Just subst
                  Just subst' -> combineManySubstitutions nullSpan [subst, subst'] >>= (return . Just)
            _ -> return Nothing

    unify (SubstC c') (SubstT t) = unify (SubstT t) (SubstC c')
    unify (SubstC c) (SubstC c') = unify c c'
    unify (SubstK k) (SubstK k') = unify k k'
    unify _ _ = return Nothing

instance Unifiable Type where
    unify (TyVar v) t = return $ Just [(v, SubstT t)]
    unify t (TyVar v) = return $ Just [(v, SubstT t)]
    unify (FunTy _ t1 t2) (FunTy _ t1' t2') = do
        u1 <- unify t1 t1'
        u2 <- unify t2 t2'
        u1 <<>> u2
    unify (TyCon c) (TyCon c') | c == c' = return $ Just []
    unify (Box c t) (Box c' t') = do
        u1 <- unify c c'
        u2 <- unify t t'
        u1 <<>> u2
    unify (Diamond e t) (Diamond e' t') = do
        u1 <- unify e e'
        u2 <- unify t t'
        u1 <<>> u2
    unify (TyApp t1 t2) (TyApp t1' t2') = do
        u1 <- unify t1 t1'
        u2 <- unify t2 t2'
        u1 <<>> u2
    unify (TyInt i) (TyInt j) | i == j = return $ Just []
    unify t@(TyInfix o t1 t2) t'@(TyInfix o' t1' t2') = do
        st <- get
        (k, _) <- synthKind nullSpan (tyVarContext st) t
        (k', _) <- synthKind nullSpan (tyVarContext st) t
        jK <- joinKind k k'
        case jK of
            Just (KPromote (TyCon (internalName -> "Nat")), _) -> do
                c  <- compileNatKindedTypeToCoeffect nullSpan t
                c' <- compileNatKindedTypeToCoeffect nullSpan t'
                addConstraint $ Eq nullSpan c c' (TyCon $ mkId "Nat")
                return $ Just []

            _ | o == o' -> do
                u1 <- unify t1 t1'
                u2 <- unify t2 t2'
                u1 <<>> u2
            -- No unification
            _ -> return $ Nothing
    -- No unification
    unify _ _ = return $ Nothing

instance Unifiable Coeffect where
    unify (CVar v) c = do
        checkerState <- get
        subst <- case lookup v (tyVarContext checkerState) of
            -- If the coeffect variable has a poly kind then update it with the
            -- kind of c
            Just ((KVar kv), q) -> do
                    (coeffTy, subst) <- inferCoeffectType nullSpan c
                    put $ checkerState { tyVarContext = replace (tyVarContext checkerState)
                                                                    v (promoteTypeToKind coeffTy, q) }
                    return subst

            Just (k, q) ->
                case c of
                    CVar v' ->
                        case lookup v' (tyVarContext checkerState) of
                            Just (KVar _, q) -> do
                                -- The type of v is known and c is a variable with a poly kind
                                put $ checkerState
                                    { tyVarContext = replace (tyVarContext checkerState) v' (k, q) }
                                return []
                            _ -> return []
                    _ -> return []
            Nothing -> return []
        -- Standard result of unifying with a variable
        return $ Just $ subst ++ [(v, SubstC c)]

    unify c (CVar v) = unify (CVar v) c
    unify (CPlus c1 c2) (CPlus c1' c2') = do
        u1 <- unify c1 c1'
        u2 <- unify c2 c2'
        u1 <<>> u2

    unify (CTimes c1 c2) (CTimes c1' c2') = do
        u1 <- unify c1 c1'
        u2 <- unify c2 c2'
        u1 <<>> u2

    unify (CMeet c1 c2) (CMeet c1' c2') = do
        u1 <- unify c1 c1'
        u2 <- unify c2 c2'
        u1 <<>> u2

    unify (CJoin c1 c2) (CJoin c1' c2') = do
        u1 <- unify c1 c1'
        u2 <- unify c2 c2'
        u1 <<>> u2

    unify (CInfinity k) (CInfinity k') = do
        unify k k'

    unify (CZero k) (CZero k') = do
        unify k k'

    unify (COne k) (COne k') = do
        unify k k'

    unify (CSet tys) (CSet tys') = do
        ums <- zipWithM (\x y -> unify (snd x) (snd y)) tys tys'
        foldM (<<>>) (Just []) ums

    unify (CSig c ck) (CSig c' ck') = do
        u1 <- unify c c'
        u2 <- unify ck ck'
        u1 <<>> u2

    unify c c' =
        if c == c' then return $ Just [] else return Nothing

instance Unifiable Kind where
    unify (KVar v) k =
        return $ Just [(v, SubstK k)]
    unify k (KVar v) =
        return $ Just [(v, SubstK k)]
    unify (KFun k1 k2) (KFun k1' k2') = do
        u1 <- unify k1 k1'
        u2 <- unify k2 k2'
        u1 <<>> u2
    unify k k' = return $ if k == k' then Just [] else Nothing

instance Unifiable t => Unifiable (Maybe t) where
    unify Nothing _ = return (Just [])
    unify _ Nothing = return (Just [])
    unify (Just x) (Just y) = unify x y

updateTyVar :: (?globals :: Globals) => Span -> Id -> Kind -> Checker ()
updateTyVar s tyVar k = do
    -- CLEAN
    --liftIO $ putStrLn $ "updating " <> pretty tyVar <> " to " <> pretty k
    -- Updated the kind of type variable `v` in the context
    st <- get
    -- Get the current quantification
    case lookup tyVar (tyVarContext st) of
      Just (_, q) -> do
          st <- get
          -- liftIO $ putStrLn $ "\n\ntyVarContext before = " <> pretty (tyVarContext st)
          modify (\st -> st{ tyVarContext = rewriteCtxt (tyVarContext st) })
          st <- get
          -- liftIO $ putStrLn $ "\ntyVarContext after = " <> pretty (tyVarContext st)
          -- Rewrite the predicate
          st <- get
          let subst = case k of
                        KPromote t -> [(tyVar, SubstT t)]
                        _          -> [(tyVar, SubstK k)]
          ps <- mapM (substitute subst) (predicateStack st)
          put st{ predicateStack = ps }

          {- }
          case demoteKindToType k of
              Nothing -> return ()
              Just t -> do
                  ps <- mapM (substitute [(v, SubstK t, q))])
                  modify (\st -> st{ predicateStack = map (rewriteBindersInPredicate [(v, (t, q))])
                                                          (predicateStack st)})
  -}
      Nothing -> throw UnboundVariableError{ errLoc = s, errId = tyVar }
  where
    rewriteCtxt :: Ctxt (Kind, Quantifier) -> Ctxt (Kind, Quantifier)
    rewriteCtxt [] = []
    rewriteCtxt ((name, (KPromote (TyVar kindVar), q)) : ctxt)
     | tyVar == kindVar = (name, (k, q)) : rewriteCtxt ctxt
    rewriteCtxt ((name, (KVar kindVar, q)) : ctxt)
     | tyVar == kindVar = (name, (k, q)) : rewriteCtxt ctxt
    rewriteCtxt (x : ctxt) = x : rewriteCtxt ctxt


--------------------------------------------------------------------------------
-- Below this point is the KindsAlgorithmic module, moved here to temporarily --
-- get around cyclic module dependencies.                                     --
--------------------------------------------------------------------------------

-- module Language.Granule.Checker.KindsAlgorithmic(checkKind, kindCheckDef, synthKind) where

-- | Check the kind of a definition
-- Currently we expect that a type scheme has kind KType
kindCheckDef :: (?globals :: Globals) => Def v t -> Checker (Def v t)
kindCheckDef (Def s id rf eqs (Forall s' quantifiedVariables constraints ty)) = do
  -- Set up the quantified variables in the type variable context
  modify (\st -> st { tyVarContext = map (\(n, c) -> (n, (c, ForallQ))) quantifiedVariables })
  st <- get
  forM_ constraints $ \constraint -> checkKind s (tyVarContext st) constraint KPredicate

  st <- get
  ty <- return $ replaceSynonyms ty
  unifiers <- checkKind s (tyVarContext st) ty KType

  -- Rewrite the quantified variables with their possibly updated kinds (inferred)
  qVars <- mapM (\(v, a) -> substitute unifiers a >>= (\b -> return (v, b))) quantifiedVariables
  modify (\st -> st { tyVarContext = [] })

  -- Update the def with the resolved quantifications
  return (Def s id rf eqs (Forall s' qVars constraints ty))

-- Replace any constructor IDs with their top-element
-- (i.e., IO gets replaces with the set of all effects as an alias)
replaceSynonyms :: Type -> Type
replaceSynonyms = runIdentity . typeFoldM (baseTypeFold { tfTyCon = conCase })
  where
    conCase conId =
      return $ case effectTop (TyCon conId) of
        Just ty -> ty
        Nothing -> TyCon conId

checkKind :: (?globals :: Globals) =>
  Span -> Ctxt (Kind, Quantifier) -> Type -> Kind -> Checker Substitution

-- KChk_funk
checkKind s ctxt (FunTy _ t1 t2) KType = do
  subst1 <- checkKind s ctxt t1 KType
  subst2 <- checkKind s ctxt t2 KType
  combineSubstitutions s subst1 subst2

-- KChk_app
checkKind s ctxt (TyApp t1 t2) k2 = do
  (k1, subst1) <- synthKind s ctxt t2
  subst2 <- checkKind s ctxt t1 (KFun k1 k2)
  combineSubstitutions s subst1 subst2

-- KChk_opRing and KChk_effOp combined (i.e. closed operators)
checkKind s ctxt t@(TyInfix op t1 t2) k | closedOperation op = do
  maybeSubst <- closedOperatorAtKind s ctxt op k
  case maybeSubst of
    Just subst3 -> do
      subst1 <- checkKind s ctxt t1 k
      subst2 <- checkKind s ctxt t2 k
      combineManySubstitutions s [subst1, subst2, subst3]
    Nothing -> throw OperatorUndefinedForKind { errLoc = s, errTyOp = op, errK = k }

-- KChk_coeffZero and KChk_coeffOne combined
checkKind s ctxt (TyInt n) (KPromote r) | n == 0 || n == 1 = checkKind s ctxt r KCoeffect

-- KChk_effOne
checkKind s ctxt (TyInt 1) (KPromote r) = checkKind s ctxt r KEffect

-- KChk_set
{-checkKind s ctxt (TySet ts) k = do
  substs <- foldrM (\t res -> (:res) <$> checkKind s ctxt t k) [] ts
  combineManySubstitutions s substs-}

-- KChk_union
checkKind s ctxt t k@(KUnion k1 k2) =
  checkKind s ctxt t k1 `catchError` const (checkKind s ctxt t k2) `catchError` const (throw KindError { errLoc = s, errTy = t, errK = k })

-- Fall through to synthesis if checking can not be done.
checkKind s ctxt t k = do
  (k', subst) <- synthKind s ctxt t
  join <- k `joinKind` k'
  case join of
    Just (_, subst) -> return subst
    Nothing -> throw KindMismatch { errLoc = s, tyActualK = Just t, kExpected = k, kActual = k' }

synthKind :: (?globals :: Globals) =>
  Span -> Ctxt (Kind, Quantifier) -> Type -> Checker (Kind, Substitution)

-- KChkS_var and KChkS_instVar
synthKind s ctxt (TyVar x) = do
  case lookup x ctxt of
    Just (k, _) -> return (k, [])
    Nothing     -> throw $ UnboundTypeVariable { errLoc = s, errId = x }

-- KChkS_fun
synthKind s ctxt (FunTy _ t1 t2) = do
  subst1 <- checkKind s ctxt t1 KType
  subst2 <- checkKind s ctxt t2 KType
  subst <- combineSubstitutions s subst1 subst2
  return (KType, subst)

-- KChkS_app
synthKind s ctxt (TyApp t1 t2) = do
  (funK, subst1) <- synthKind s ctxt t1
  case funK of
    (KFun k1 k2) -> do
      subst2 <- checkKind s ctxt t2 k1
      subst <- combineSubstitutions s subst1 subst2
      return (k2, subst)
    _ -> throw KindError { errLoc = s, errTy = t1, errK = funK }

-- KChkS_predOp
synthKind s ctxt (TyInfix op t1 t2) | predicateOperation op = do
  (k, subst1) <- synthKind s ctxt t1
  maybeSubst <- predicateOperatorAtKind s ctxt op k
  case maybeSubst of
    Just subst3 -> do
      subst2 <- checkKind s ctxt t2 k
      subst <- combineManySubstitutions s [subst1, subst2, subst3]
      return (KPredicate, subst)
    Nothing -> throw OperatorUndefinedForKind { errLoc = s, errTyOp = op, errK = k }

-- KChkS_opRing and KChkS_effOpp
synthKind s ctxt (TyInfix op t1 t2) | closedOperation op = do
  (k, subst1) <- synthKind s ctxt t1
  maybeSubst <- closedOperatorAtKind s ctxt op k
  case maybeSubst of
    Just subst3 -> do
      subst2 <- checkKind s ctxt t2 k
      subst <- combineManySubstitutions s [subst1, subst2, subst3]
      return (k, subst)
    Nothing -> throw OperatorUndefinedForKind { errLoc = s, errTyOp = op, errK = k }

-- KChkS_effOne, KChkS_coeffZero and KChkS_coeffOne
synthKind s ctxt (TyInt n) = return (KPromote (TyCon (Id "Nat" "Nat")), [])

-- KChkS_box
synthKind s ctxt (Box c t) = do
  _ <- inferCoeffectType s c
  subst <- checkKind s ctxt t KType
  return (KType, subst)

-- KChkS_dia
synthKind s ctxt (Diamond e t) = do
  (kB, subst2) <- synthKind s ctxt e
  case kB of
    (KPromote b) -> do
      st <- get
      subst1 <- checkKind s (tyVarContext st) b KEffect
      subst3 <- checkKind s (tyVarContext st) t KType
      subst <- combineManySubstitutions s [subst1, subst2, subst3]
      return (KType, subst)
    _ -> throw KindError { errLoc = s, errTy = e, errK = kB }

synthKind s ctxt (TyCon (internalName -> "Pure")) = do
  -- Create a fresh type variable
  var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") KEffect
  return (KPromote $ TyVar var, [])

-- KChkS_int and KChkS_char (and other base types)
synthKind s ctxt (TyCon id) = do
  st <- get
  case lookup id (typeConstructors st) of
      Just (kind, _, _) -> return (kind, [])
      Nothing -> do
        mConstructor <- lookupDataConstructor s id
        case mConstructor of
          Just (Forall _ [] [] t, _) -> return (KPromote t, [])
          Just _ -> error $ pretty s <> "I'm afraid I can't yet promote the polymorphic data constructor:"  <> pretty id
          Nothing -> throw UnboundTypeConstructor { errLoc = s, errId = id }

-- KChkS_set
synthKind s ctxt (TySet (t:ts)) = do
  (k, subst1) <- synthKind s ctxt t
  substs <- foldrM (\t' res -> (:res) <$> checkKind s ctxt t' k) [] ts
  subst <- combineManySubstitutions s (subst1:substs)
  case lookup k setElements of
    -- Lift this alias to the kind level
    Just t -> return (KPromote t, subst)
    Nothing ->
      -- Return a set type lifted to a kind
      case demoteKindToType k of
        Just t -> return (KPromote $ TyApp (TyCon $ mkId "Set") t, subst)
        -- If the kind cannot be demoted then we shouldn't be making a set
        Nothing -> throw KindCannotFormSet { errLoc = s,  errK = k }

synthKind s _ t = do
  debugM "Can't synth" (pretty t)
  throw ImpossibleKindSynthesis { errLoc = s, errTy = t }

-- | `closedOperatorAtKind` takes an operator `op` and a kind `k` and returns a
-- substitution if this is a valid operator at kind `k -> k -> k`.
closedOperatorAtKind :: (?globals :: Globals) =>
  Span -> Ctxt (Kind, Quantifier) -> TypeOperator -> Kind -> Checker (Maybe Substitution)

-- Nat case
closedOperatorAtKind _ _ op (KPromote (TyCon (internalName -> "Nat"))) =
  return $ if closedOperation op then Just [] else Nothing

-- * case
closedOperatorAtKind s ctxt TyOpTimes (KPromote t) = do
  -- See if the type is a coeffect
  (result, putChecker) <- peekChecker (checkKind s ctxt t KCoeffect)
  case result of
    Left _ -> do
      -- If not, see if the type is an effect
      (result', putChecker') <- peekChecker (checkKind s ctxt t KEffect)
      case result' of
        -- Not a closed operator at this kind
        Left  _ -> return Nothing
        -- Yes it is an effect type
        Right subst -> do
          putChecker'
          return $ Just subst
    -- Yes it is a coeffect type
    Right subst -> do
      putChecker
      return $ Just subst

-- Any other "coeffect operators" case
closedOperatorAtKind s ctxt op (KPromote t) | coeffectResourceAlgebraOps op = do
  -- See if the type is a coeffect
  (result, putChecker) <- peekChecker (checkKind s ctxt t KCoeffect)
  case result of
    Left _ -> return Nothing
    Right subst -> do
      putChecker
      return $ Just subst

-- TODO: Investigate the consequences of this.
closedOperatorAtKind _ _ op (KVar _) = do
  return $ if closedOperation op then Just [] else Nothing

closedOperatorAtKind _ _ _ _ = return Nothing

-- | `predicateOperatorAtKind` takes an operator `op` and a kind `k` and returns
-- a substitution if this is a valid operator at kind `k -> k -> KPredicate`.
predicateOperatorAtKind :: (?globals :: Globals) =>
  Span -> Ctxt (Kind, Quantifier) -> TypeOperator -> Kind -> Checker (Maybe Substitution)
predicateOperatorAtKind s ctxt op (KPromote t) | predicateOperation op = do
  (result, putChecker) <- peekChecker (checkKind s ctxt t KCoeffect)
  case result of
    Left _ -> return Nothing
    Right subst -> do
      putChecker
      return $ Just subst
predicateOperatorAtKind _ _ _ _ = return Nothing

-- | Determines if a type operator produces results of kind KPredicate.
predicateOperation :: TypeOperator -> Bool
predicateOperation op = (\(_, _, c) -> c) (tyOps op) == KPredicate

-- | Compute the join of two kinds, if it exists
joinKind :: (?globals :: Globals) => Kind -> Kind -> Checker (Maybe (Kind, Substitution))

joinKind k1 k2 | k1 == k2 = return $ Just (k1, [])

joinKind (KVar v) k = do
  st <- get
  case (lookup v (tyVarContext st)) of
    Just (_, q) | q == InstanceQ || q == BoundQ -> return $ Just (k, [(v, SubstK k)])
    -- Occurs if an implicitly quantified variable has arisen
    Nothing -> return $ Just (k, [(v, SubstK k)])
    -- Don't unify with universal variables
    _  -> return Nothing

joinKind k (KVar v) = do
  st <- get
  case (lookup v (tyVarContext st)) of
    Just (_, q) | q == InstanceQ || q == BoundQ -> return $ Just (k, [(v, SubstK k)])
    -- Occurs if an implicitly quantified variable has arisen
    Nothing -> return $ Just (k, [(v, SubstK k)])
    -- Don't unify with universal variables
    _  -> return Nothing

joinKind (KPromote t1) (KPromote t2) = do
  (coeffTy, subst, _) <- mguCoeffectTypes nullSpan t1 t2
  return $ Just (KPromote coeffTy, subst)

joinKind (KUnion k1 k2) k = do
  jK1 <- joinKind k k1
  case jK1 of
    Nothing -> do
        jK2 <- joinKind k k2
        case jK2 of
            Nothing -> return $ Nothing
            Just (k2', u) -> return $ Just (KUnion k1 k2', u)
    Just (k1', u) -> return $ Just (KUnion k1' k2, u)

joinKind k (KUnion k1 k2) = joinKind (KUnion k1 k2) k

joinKind (KFun k1 k2) (KFun k3 k4) = do
  jK1 <- joinKind k1 k3
  jK2 <- joinKind k2 k4
  case (jK1, jK2) of
    (Just (k5, subst1), Just (k6, subst2)) -> do
      subst <- combineSubstitutions nullSpan subst1 subst2
      return $ Just (KFun k5 k6, subst)
    _ -> return Nothing

joinKind _ _ = return Nothing

-- | Infer the type of a coeffect term (giving its span as well)
inferCoeffectType :: (?globals :: Globals) => Span -> Coeffect -> Checker (Type, Substitution)
inferCoeffectType s c = do
  st <- get
  inferCoeffectTypeInContext s (map (\(id, (k, _)) -> (id, k)) (tyVarContext st)) c

inferCoeffectTypeInContext :: (?globals :: Globals) => Span -> Ctxt Kind -> Coeffect -> Checker (Type, Substitution)
-- Coeffect constants have an obvious kind
inferCoeffectTypeInContext _ _ (Level _) = return (TyCon $ mkId "Level", [])
inferCoeffectTypeInContext _ _ (CNat _) = return (TyCon $ mkId "Nat", [])
inferCoeffectTypeInContext _ _ (CFloat _) = return (TyCon $ mkId "Q", [])
inferCoeffectTypeInContext _ _ (CSet _) = return (TyCon $ mkId "Set", [])
inferCoeffectTypeInContext s ctxt (CProduct c1 c2)    = do
  (k1, subst1) <- inferCoeffectTypeInContext s ctxt c1
  (k2, subst2) <- inferCoeffectTypeInContext s ctxt c2
  subst <- combineSubstitutions s subst1 subst2
  return $ (TyApp (TyApp (TyCon $ mkId "×") k1) k2, subst)

inferCoeffectTypeInContext s ctxt (CInterval c1 c2)    = do
  (k, substitution, _) <- mguCoeffectTypesFromCoeffects s c1 c2
  return $ (TyApp (TyCon $ mkId "Interval") k, substitution)

-- Take the join for compound coeffect epxressions
inferCoeffectTypeInContext s _ (CPlus c c')  = fst2 <$> mguCoeffectTypesFromCoeffects s c c'
inferCoeffectTypeInContext s _ (CMinus c c') = fst2 <$> mguCoeffectTypesFromCoeffects s c c'
inferCoeffectTypeInContext s _ (CTimes c c') = fst2 <$> mguCoeffectTypesFromCoeffects s c c'
inferCoeffectTypeInContext s _ (CMeet c c')  = fst2 <$> mguCoeffectTypesFromCoeffects s c c'
inferCoeffectTypeInContext s _ (CJoin c c')  = fst2 <$> mguCoeffectTypesFromCoeffects s c c'
inferCoeffectTypeInContext s _ (CExpon c c') = fst2 <$> mguCoeffectTypesFromCoeffects s c c'

-- Coeffect variables should have a type in the cvar->kind context
inferCoeffectTypeInContext s ctxt (CVar cvar) = do
  st <- get
  case lookup cvar ctxt of
    Nothing -> do
      throw UnboundTypeVariable{ errLoc = s, errId = cvar }
      -- state <- get
      -- let newType = TyVar $ "ck" <> show (uniqueVarId state)
      -- We don't know what it is yet though, so don't update the coeffect kind ctxt
      -- put (state { uniqueVarId = uniqueVarId state + 1 })
      -- return newType
    Just (KVar name) -> return $ (TyVar name, [])
    Just (KPromote t) -> checkKind s (universify ctxt) t KCoeffect >> return (t, [])
    Just k -> throw
      KindMismatch{ errLoc = s, tyActualK = Just $ TyVar cvar, kExpected = KPromote (TyVar $ mkId "coeffectType"), kActual = k }

inferCoeffectTypeInContext s ctxt (CZero t) = checkKind s (universify ctxt) t KCoeffect >> return (t, [])
inferCoeffectTypeInContext s ctxt (COne t)  = checkKind s (universify ctxt) t KCoeffect >> return (t, [])
inferCoeffectTypeInContext s ctxt (CInfinity (Just t)) = checkKind s (universify ctxt) t KCoeffect >> return (t, [])
-- Unknown infinity defaults to the interval of extended nats version
inferCoeffectTypeInContext s ctxt (CInfinity Nothing) = return (TyApp (TyCon $ mkId "Interval") extendedNat, [])
inferCoeffectTypeInContext s ctxt (CSig _ t) = checkKind s (universify ctxt) t KCoeffect >> return (t, [])

fst2 :: (a, b, c) -> (a, b)
fst2 (x, y, _) = (x, y)

inferCoeffectTypeAssumption :: (?globals :: Globals) =>
  Span -> Assumption -> Checker (Maybe Type, Substitution)
inferCoeffectTypeAssumption _ (Linear _) = return (Nothing, [])
inferCoeffectTypeAssumption s (Discharged _ c) = do
    (t, subst) <- inferCoeffectType s c
    return $ (Just t, subst)

-- Find the most general unifier of two coeffects
-- This is an effectful operation which can update the coeffect-kind
-- contexts if a unification resolves a variable
mguCoeffectTypesFromCoeffects :: (?globals :: Globals)
  => Span
  -> Coeffect
  -> Coeffect
  -> Checker (Type, Substitution, (Coeffect -> Coeffect, Coeffect -> Coeffect))
mguCoeffectTypesFromCoeffects s c1 c2 = do
  -- TODO: Need to not throw away the substitution here
  (coeffTy1, _) <- inferCoeffectType s c1
  (coeffTy2, _) <- inferCoeffectType s c2
  mguCoeffectTypes s coeffTy1 coeffTy2

-- Universally quantifies everything in a context.
universify :: Ctxt a -> Ctxt (a, Quantifier)
universify = map (second (\k -> (k, ForallQ)))
