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
  checkKind,
  combineSubstitutions,
  combineManySubstitutions,
  freshPolymorphicInstance,
  inferCoeffectType,
  inferCoeffectTypeAssumption,
  joinKind,
  kindCheckDef,
  mguCoeffectTypesFromCoeffects,
  replaceSynonyms,
  synthKind,
  updateTyVar) where

import Control.Arrow (second)
import Control.Monad
import Control.Monad.Except (catchError)
import Control.Monad.State.Strict
import Data.Bifunctor.Foldable (bicataM)
import Data.Foldable (foldrM)
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

import Language.Granule.Checker.Effects (effectTop)
import Language.Granule.Checker.Flatten (mguCoeffectTypes)
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

instance Substitutable (Type l) where
  substitute subst (Type l) =
    return $ Type l

  substitute subst (FunTy name t1 t2) = do
    t1' <- substitute subst t1
    t2' <- substitute subst t2
    return $ FunTy name t1' t2'

  substitute subst (TyCon name) =
    return $ TyCon name

  substitute subst (Box c t) = do
    t' <- substitute subst t
    return $ Box c t'

  substitute subst (Diamond e t) = do
    t' <- substitute subst t
    return $ Diamond e t'

  substitute subst (TyVar v) =
    return $ TyVar v

  substitute subst (TyApp t1 t2) = do
    t1' <- substitute subst t1
    t2' <- substitute subst t2
    return $ TyApp t1' t2'

  substitute subst (TyInt n) =
    return $ TyInt n

  substitute subst (TyRational n) =
    return $ TyRational n

  substitute subst (TyInfix op t1 t2) = do
    t1' <- substitute subst t1
    t2' <- substitute subst t2
    return $ TyInfix op t1' t2'

  substitute subst (TySet elems) = do
    elems' <- mapM (substitute subst) elems
    return $ TySet elems'

  substitute subst (TyCase guard cases) = do
    guard' <- substitute subst guard
    cases' <- mapM (\(pat, branch) -> do
                        pat' <- substitute subst pat
                        branch' <- substitute subst branch
                        return (pat', branch')) cases
    return $ TyCase guard' cases'


  substitute subst (TySig t1 t2) = do
    t1' <- substitute subst t1
    t2' <- substitute subst t2
    return $ TySig t1' t2'

{-
instance Substitutable (Type Zero) where
  substitute subst s = typeFoldM0 (baseTypeFoldZero
                                { tfTyVar0 = varSubst
                                , tfBox0 = box }) s >>= (return . normaliseType)
      where
        box c t = do
          c <- substitute subst c
          mBox c t

        varSubst v =
          case lookup v subst of
            Just (SubstT t) -> return t
            _               -> mTyVar v

instance Substitutable (Type One) where
  substitute subst = typeFoldM1 (baseTypeFoldOne
                                { tfTyVar1 = varSubst })
      where
        varSubst v =
          case lookup v subst of
            Just (SubstK t) -> return t
            Just (SubstT t) -> tryTyPromote nullSpan t
            _               -> mTyVar v

instance Substitutable (Type Two) where
  substitute _ = error "TODO: Cannot currently substitute into Sorts"
-}

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
removeReflexivePairs ((v, SubstK (TyVar v')):subst) | v == v' = removeReflexivePairs subst
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

-- | Apply a name map to a type to rename the type variables
renameType :: (?globals :: Globals) => [(Id, Id)] -> Type Zero -> Checker (Type Zero)
renameType subst = typeFoldM0 $ baseTypeFoldZero
  { tfBox0   = renameBox subst
  , tfTyVar0 = renameTyVar subst
  }
  where
    renameBox renameMap c t = do
      c' <- substitute (map (\(v, var) -> (v, SubstT $ TyVar var)) renameMap) c
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
  => Quantifier   -- ^ Variety of quantifier to resolve universals into (InstanceQ or BoundQ)
  -> Bool         -- ^ Flag on whether this is a data constructor-- if true, then be careful with existentials
  -> TypeScheme   -- ^ Type scheme to freshen
  -> Substitution -- ^ A substitution associated with this type scheme (e.g., for
                  --     data constructors of indexed types) that also needs freshening

  -> Checker (Type Zero, Ctxt Kind, Substitution, [Type Zero], Substitution)
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

instance Substitutable (Equation () (Type Zero)) where
  substitute ctxt (Equation sp name ty rf patterns expr) =
      do ty' <- substitute ctxt ty
         pat' <- mapM (substitute ctxt) patterns
         expr' <- substitute ctxt expr
         return $ Equation sp name ty' rf pat' expr'

substituteValue :: (?globals::Globals)
                => Substitution
                -> ValueF ev (Type Zero) (Value ev (Type Zero)) (Expr ev (Type Zero))
                -> Checker (Value ev (Type Zero))
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
               -> ExprF ev (Type Zero) (Expr ev (Type Zero)) (Value ev (Type Zero))
               -> Checker (Expr ev (Type Zero))
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

instance Substitutable (Expr () (Type Zero)) where
  substitute ctxt = bicataM (substituteExpr ctxt) (substituteValue ctxt)

instance Substitutable (Value () (Type Zero)) where
  substitute ctxt = bicataM (substituteValue ctxt) (substituteExpr ctxt)

instance Substitutable (Pattern (Type Zero)) where
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
    unify (SubstK k) (SubstK k') = unify k k'
    unify _ _ = return Nothing

instance Unifiable (Type Zero) where
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
            Just (TyCon (internalName -> "Nat"), _) -> do
                addConstraint $ Eq nullSpan t t' (TyCon $ mkId "Nat")
                return $ Just []

            _ | o == o' -> do
                u1 <- unify t1 t1'
                u2 <- unify t2 t2'
                u1 <<>> u2
            -- No unification
            _ -> return $ Nothing
    -- No unification
    unify _ _ = return $ Nothing

instance Unifiable Kind where
    unify (TyVar v) k =
        return $ Just [(v, SubstK k)]
    unify k (TyVar v) =
        return $ Just [(v, SubstK k)]
    unify (FunTy _ k1 k2) (FunTy _ k1' k2') = do
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
    rewriteCtxt :: Ctxt (TypeWithLevel, Quantifier) -> Ctxt (TypeWithLevel, Quantifier)
    rewriteCtxt [] = []
    rewriteCtxt ((name, (TypeWithLevel (LSucc LZero) (TyVar kindVar), q)) : ctxt)
     | tyVar == kindVar = (name, (TypeWithLevel (LSucc LZero) k, q)) : rewriteCtxt ctxt
    rewriteCtxt ((name, (TypeWithLevel (LSucc LZero) (TyVar kindVar), q)) : ctxt)
     | tyVar == kindVar = (name, (TypeWithLevel (LSucc LZero) k, q)) : rewriteCtxt ctxt
    rewriteCtxt (x : ctxt) = x : rewriteCtxt ctxt

--------------------------------------------------------------------------------
-- Below this point is the KindsAlgorithmic module, moved here to temporarily --
-- get around cyclic module dependencies.                                     --
--------------------------------------------------------------------------------

-- module Language.Granule.Checker.KindsAlgorithmic where

-- | Check the kind of a definition
-- Currently we expect that a type scheme has kind ktype
kindCheckDef :: (?globals :: Globals) => Def v t -> Checker (Def v t)
kindCheckDef (Def s id rf eqs (Forall s' quantifiedVariables constraints ty)) = do
  let localTyVarContext = universify quantifiedVariables

  -- Set up the quantified variables in the type variable context
  modify (\st -> st { tyVarContext = localTyVarContext })
  forM_ constraints $ \constraint -> checkKind s localTyVarContext constraint kpredicate

  ty <- return $ replaceSynonyms ty
  unifiers <- checkKind s localTyVarContext ty ktype

  -- Rewrite the quantified variables with their possibly updated kinds (inferred)
  qVars <- mapM (\(v, a) -> substitute unifiers a >>= (\b -> return (v, b))) quantifiedVariables
  modify (\st -> st { tyVarContext = [] })

  -- Update the def with the resolved quantifications
  return (Def s id rf eqs (Forall s' qVars constraints ty))

-- Replace any constructor IDs with their top-element
-- (i.e., IO gets replaces with the set of all effects as an alias)
replaceSynonyms :: Type Zero -> Type Zero
replaceSynonyms = runIdentity . typeFoldM0 (baseTypeFoldZero { tfTyCon0 = conCase })
  where
    conCase conId = let tyConId = TyCon conId in return $ fromMaybe tyConId (effectTop tyConId)

checkKind :: (?globals :: Globals) =>
  Span -> Ctxt (TypeWithLevel, Quantifier) -> Type l -> Type (Succ l) -> Checker Substitution

-- KChk_funk
checkKind s ctxt (FunTy _ t1 t2) k = do
  subst1 <- checkKind s ctxt t1 k
  subst2 <- checkKind s ctxt t2 k
  combineSubstitutions s subst1 subst2

-- KChk_app
checkKind s ctxt (TyApp t1 t2) k2 = do
  (k1, subst1) <- synthKind s ctxt t2
  subst2 <- checkKind s ctxt t1 (FunTy Nothing k1 k2)
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
checkKind s ctxt (TyInt 0) t =
  case t of
    -- 0 : Nat
    TyCon (internalName -> "Nat") -> return []
    -- 0 : R if R : Coeffect
    _ -> checkKind s ctxt t kcoeffect

-- KChk_effOne
checkKind s ctxt (TyInt 1) t =
  case t of
    -- 1 : Nat
    TyCon (internalName -> "Nat") -> return []
    -- 1 : R if R : Coeffect or R : Effect
    _ -> (checkKind s ctxt t kcoeffect) <|> (checkKind s ctxt t keffect)

-- KChk_sig
checkKind s ctxt (TySig t k) k' = do
  join <- k `joinKind` k'
  case join of
    Just (_, subst) -> return subst
    Nothing -> throw KindMismatch { errLoc = s, tyActualK = Just t, kExpected = k, kActual = k' }

-- KChck_Nat
-- "Nat" belonds to Coeffect, Effect, and Type kinds
checkKind s ctxt (TyCon (internalName -> "Nat")) (TyCon (internalName -> "Coeffect")) =
  return []
checkKind s ctxt (TyCon (internalName -> "Nat")) (TyCon (internalName -> "Effect")) =
  return []
checkKind s ctxt (TyCon (internalName -> "Nat")) (Type (LSucc LZero)) =
  return []

-- Fall through to synthesis if checking can not be done.
checkKind s ctxt t k = do
  (k', subst1) <- synthKind s ctxt t
  join <- k `joinKind` k'
  case join of
    Just (_, subst2) -> combineSubstitutions s subst1 subst2
    Nothing -> throw KindMismatch { errLoc = s, tyActualK = Just t, kExpected = k, kActual = k' }

synthKind :: (?globals :: Globals) =>
  Span -> Ctxt (TypeWithLevel, Quantifier) -> Type l -> Checker (Type (Succ l), Substitution)

-- KChkS_var and KChkS_instVar
synthKind s ctxt t@(TyVar x) = do
  m <- lookupAtLevel s x ctxt (LSucc (getLevel t))
  case m of
    Just k -> return (k, [])
    Nothing     -> throw UnboundTypeVariable { errLoc = s, errId = x }

-- -- KChkS_fun
-- synthKind s ctxt (FunTy _ t1 t2) = do
--   subst1 <- checkKind s ctxt t1 ktype
--   subst2 <- checkKind s ctxt t2 ktype
--   subst <- combineSubstitutions s subst1 subst2
--   return (ktype, subst)

-- KChkS_app
synthKind s ctxt (TyApp t1 t2) = do
  (funK, subst1) <- synthKind s ctxt t1
  case funK of
    (FunTy _ k1 k2) -> do
      subst2 <- checkKind s ctxt t2 k1
      subst <- combineSubstitutions s subst1 subst2
      return (k2, subst)
    _ -> throw KindError { errLoc = s, errTyL = typeWithLevel t1, errKL = typeWithLevel funK }

-- KChkS_predOp
synthKind s ctxt (TyInfix op t1 t2) | predicateOperation op = do
  (k, subst1) <- synthKind s ctxt t1
  maybeSubst <- predicateOperatorAtKind s ctxt op k
  case maybeSubst of
    Just subst3 -> do
      subst2 <- checkKind s ctxt t2 k
      subst <- combineManySubstitutions s [subst1, subst2, subst3]
      return (kpredicate, subst)
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
synthKind s ctxt (TyInt n) = return (TyCon (Id "Nat" "Nat"), [])

-- KChkS_box
synthKind s ctxt (Box c t) = do
  (innerK, subst2) <- synthKind s ctxt c
  st <- get
  subst1 <- checkKind s (tyVarContext st) innerK kcoeffect
  subst3 <- checkKind s (tyVarContext st) t ktype
  subst <- combineManySubstitutions s [subst1, subst2, subst3]
  return (ktype, subst)

-- KChkS_dia
synthKind s ctxt (Diamond e t) = do
  (innerK, subst2) <- synthKind s ctxt e
  st <- get
  subst1 <- checkKind s (tyVarContext st) innerK keffect
  subst3 <- checkKind s (tyVarContext st) t ktype
  subst <- combineManySubstitutions s [subst1, subst2, subst3]
  return (ktype, subst)

synthKind s ctxt (TyCon (internalName -> "Pure")) = do
  -- Create a fresh type variable
  var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") keffect
  return (TyVar var, [])

synthKind s ctxt (TyCon (internalName -> "Handled")) = do
  var <- freshTyVarInContext (mkId $ "eff[" <> pretty (startPos s) <> "]") keffect
  return $ ((FunTy Nothing (TyVar var) (TyVar var)), [])

-- KChkS_con
synthKind s ctxt t@(TyCon id) = do
  st <- get
  m <- lookupAtLevel s id (typeConstructors st) (LSucc (getLevel t))
  case m of
    Just kind' -> return (kind', [])
    Nothing -> do
      mConstructor <- lookupDataConstructor s id
      case mConstructor of
        Just (Forall _ [] [] t, _) ->
          case typePromote t of
            Just t' -> return (t', [])
            Nothing -> error $ pretty s <> "I'm afraid I can't yet promote the data constructor:"  <> pretty id
        Just _ -> error $ pretty s <> "I'm afraid I can't yet promote the polymorphic data constructor:"  <> pretty id
        Nothing -> throw UnboundTypeConstructor { errLoc = s, errId = id }

-- KChkS_set
synthKind s ctxt (TySet (t:ts)) = do
  (k, subst1) <- synthKind s ctxt t
  substs <- foldrM (\t' res -> (:res) <$> checkKind s ctxt t' k) [] ts
  subst <- combineManySubstitutions s (subst1:substs)
  case lookup k setElements of
    -- Lift this alias to the kind level
    Just t  -> return (t, subst)
    Nothing -> return (TyApp (TyCon $ mkId "Set") k, subst)

-- KChkS_sig
synthKind s ctxt (TySig t k) = do
  subst <- checkKind s ctxt t k
  return (k, subst)

synthKind s _ t = do
  debugM "Can't synth" (pretty t)
  throw ImpossibleKindSynthesis { errLoc = s, errTy = t }

-- | `closedOperatorAtKind` takes an operator `op` and a kind `k` and returns a
-- substitution if this is a valid operator at kind `k -> k -> k`.
closedOperatorAtKind :: (?globals :: Globals) =>
  Span -> Ctxt (TypeWithLevel, Quantifier) -> TypeOperator -> Kind -> Checker (Maybe Substitution)

-- Nat case
closedOperatorAtKind _ _ op (TyCon (internalName -> "Nat")) =
  return $ if closedOperation op then Just [] else Nothing

-- * case
closedOperatorAtKind s ctxt TyOpTimes t = do
  -- See if the type is a coeffect
  (result, putChecker) <- peekChecker (checkKind s ctxt t kcoeffect)
  case result of
    Left _ -> do
      -- If not, see if the type is an effect
      (result', putChecker') <- peekChecker (checkKind s ctxt t keffect)
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
closedOperatorAtKind s ctxt op t | coeffectResourceAlgebraOps op = do
  -- See if the type is a coeffect
  (result, putChecker) <- peekChecker (checkKind s ctxt t kcoeffect)
  case result of
    Left _ -> return Nothing
    Right subst -> do
      putChecker
      return $ Just subst

closedOperatorAtKind _ _ op (TyVar _) =
  return $ if closedOperation op then Just [] else Nothing

closedOperatorAtKind _ _ _ _ = return Nothing

-- | `predicateOperatorAtKind` takes an operator `op` and a kind `k` and returns
-- a substitution if this is a valid operator at kind `k -> k -> kpredicate`.
predicateOperatorAtKind :: (?globals :: Globals) =>
  Span -> Ctxt (TypeWithLevel, Quantifier) -> TypeOperator -> Type l -> Checker (Maybe Substitution)
predicateOperatorAtKind s ctxt op t | predicateOperation op = do
  (result, putChecker) <- peekChecker (checkKind s ctxt t kcoeffect)
  case result of
    Left _ -> return Nothing
    Right subst -> do
      putChecker
      return $ Just subst
predicateOperatorAtKind s ctxt op k@(TyVar _) =
    return $ if predicateOperation op then Just [] else Nothing
predicateOperatorAtKind _ _ _ _ = return Nothing

-- | Determines if a type operator produces results of kind kpredicate.
predicateOperation :: TypeOperator -> Bool
predicateOperation op = (\(_, _, c) -> c) (tyOps op) == kpredicate

-- | Compute the join of two kinds, if it exists
joinKind :: (?globals :: Globals) => Kind -> Kind -> Checker (Maybe (Kind, Substitution))

joinKind k1 k2 | k1 == k2 = return $ Just (k1, [])

joinKind (TyVar v) k = do
  st <- get
  case lookup v (tyVarContext st) of
    Just (_, q) | q == InstanceQ || q == BoundQ -> return $ Just (k, [(v, SubstK k)])
    -- Occurs if an implicitly quantified variable has arisen
    Nothing -> return $ Just (k, [(v, SubstK k)])
    -- Don't unify with universal variables
    _ -> return Nothing

joinKind k1 k2@(TyVar _) = joinKind k2 k1

joinKind (FunTy _ k1 k2) (FunTy _ k3 k4) = do
  jK1 <- joinKind k1 k3
  jK2 <- joinKind k2 k4
  case (jK1, jK2) of
    (Just (k5, subst1), Just (k6, subst2)) -> do
      subst <- combineSubstitutions nullSpan subst1 subst2
      return $ Just (FunTy Nothing k5 k6, subst)
    _ -> return Nothing

joinKind _ _ = return Nothing

-- Universally quantifies everything in a context.
universify :: Ctxt Kind -> Ctxt (TypeWithLevel, Quantifier)
universify = map (second (\k -> (typeWithLevel k, ForallQ)))

-- TODO: Should this be using synthKind rather than inferCoeffectTypeInContext?
-- | Infer the type of a coeffect term (giving its span as well)
inferCoeffectType :: (?globals :: Globals) => Span -> Type Zero -> Checker (Type One, Substitution)
inferCoeffectType s c = do
  st <- get
  r <- synthKind s (tyVarContext st) c
  debugM "Inferred coeffect type" (show c <> "\n" <> show r)
  return r

inferCoeffectTypeAssumption :: (?globals :: Globals) => Span -> Assumption -> Checker (Maybe (Type One), Substitution)
inferCoeffectTypeAssumption _ (Linear _) = return (Nothing, [])
inferCoeffectTypeAssumption s (Discharged _ c) = do
  (t, subst) <- inferCoeffectType s c
  return (Just t, subst)

-- Find the most general unifier of two coeffects
-- This is an effectful operation which can update the coeffect-kind
-- contexts if a unification resolves a variable
mguCoeffectTypesFromCoeffects :: (?globals :: Globals)
  => Span
  -> Type Zero
  -> Type Zero
  -> Checker (Type One, Substitution, (Type Zero -> Type Zero, Type Zero -> Type Zero))
mguCoeffectTypesFromCoeffects s c1 c2 = do
  st <- get
  (coeffTy1, subst1) <- inferCoeffectType s c1
  (coeffTy2, subst2) <- inferCoeffectType s c2
  (coeffTy, subst3, res) <- mguCoeffectTypes s coeffTy1 coeffTy2
  subst <- combineManySubstitutions s [subst1, subst2, subst3]
  return (coeffTy, subst, res)
