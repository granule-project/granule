{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

-- Provides the core functionality for substitutions

module Language.Granule.Checker.Substitution(
  Substitutable(..),
  Unifiable(..),
  combineSubstitutions,
  combineManySubstitutions,
  freshPolymorphicInstance,
  updateTyVar,
  unify) where

import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Data.Bifunctor.Foldable (bicataM)
import Data.List (elemIndex, sortBy)
import Data.Maybe (mapMaybe)

import Language.Granule.Context

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr hiding (Substitutable)
import Language.Granule.Syntax.Helpers hiding (freshIdentifierBase)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
-- import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
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

      -- Check we're not unifying two universals to the same substitutor
      errs <- checkValid [] $ flipSubstitution $ concat uss1 
      case errs of 
        Just (v, v') -> throw $ UnificationDisallowed sp  v v' -- Change error 
        Nothing -> do
          -- Any remaining unifiers that are in u2 but not u1
          uss2 <- forM u2 $ \(v, s) ->
              case lookup v u1 of
                  Nothing -> return [(v, s)]
                  _       -> return []
          let uss = concat uss1 <> concat uss2
          return $ reduceByTransitivity uss

checkValid :: [Id] -> Substitution -> Checker (Maybe (Type, Type))
checkValid vars (sub1@(v, (SubstT (TyVar v'))):substs) = do
  st <- get
  case lookup v' (tyVarContext  st) of
    Just (_, ForallQ) -> 
      if v `elem` vars then
        return $ Just (TyVar v, TyVar v')
      else 
         checkValid (v : vars) substs
    _ -> checkValid vars substs 
checkValid vars (sub:substs) = checkValid vars substs
checkValid _ []  = return $ Nothing

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
substAssumption subst (v, Ghost c) = do
    c <- substitute subst c
    return (v, Ghost c)

-- | Get a fresh polymorphic instance of a type scheme and list of instantiated type variables
-- and their new names.
freshPolymorphicInstance :: (?globals :: Globals)
  => Quantifier   -- ^ Variety of quantifier to resolve universals into (InstanceQ or BoundQ)
  -> Bool         -- ^ Flag on whether this is a data constructor-- if true, then be careful with existentials
  -> TypeScheme   -- ^ Type scheme to freshen
  -> Substitution -- ^ A substitution associated with this type scheme (e.g., for
                  --     data constructors of indexed types) that also needs freshening
  -> [Int]
  -> Checker (Type, Ctxt Kind, Substitution, [Type], Substitution)
    -- Returns the type (with new instance variables)
       -- a context of all the instance variables kinds (and the ids they replaced)
       -- a substitution from the visible instance variable to their originals
       -- a list of the (freshened) constraints for this scheme
       -- a correspondigly freshened version of the parameter substitution
freshPolymorphicInstance quantifier isDataConstructor (Forall s kinds constr ty) ixSubstitution indices = do
   
   
    let boundTypes = typesFromIndices ty 0 indices
    debugM "freshPoly boundVars: " (show boundTypes)
 
   
    -- Universal becomes an existential (via freshCoeffeVar)
    -- since we are instantiating a polymorphic type

    renameMap <- cumulativeMapM (instantiateVariable boundTypes) kinds 

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
    instantiateVariable :: [Id] -> (Id, Kind) ->  Checker (Id, Either (Kind, Id) (Kind, Id))
    instantiateVariable boundTypes (var, k)  =
      if isDataConstructor && (var `notElem` freeVars (resultType ty))
                           && (var `notElem` freeVars (ixSubstitution))
         then do
           -- Signals an existential
           var' <- freshTyVarInContextWithBinding var k ForallQ
           -- Don't return this as a fresh skolem variable
           return (var, Right (k, var'))

         else do

           if elem var boundTypes 
             then do
               var' <- freshTyVarInContextWithBinding var k BoundQ
               return (var, Left (k, var'))
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
    

    typesFromIndices :: Type -> Int -> [Int] -> [Id]
    typesFromIndices (TyApp t1 (TyVar t2)) index indices = 
      if index `elem` indices 
        then
          t2 : typesFromIndices t1 (index+1) indices
        else
          typesFromIndices t1 (index+1) indices
    typesFromIndices (FunTy _ _ t) index indices = typesFromIndices t (index+1) indices
    typesFromIndices _ _ _ = []


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

  substitute ctxt (Hsup s c1 c2 k) = do
    c1 <- substitute ctxt c1
    c2 <- substitute ctxt c2
    k <- substitute ctxt k
    return $ Hsup s c1 c2 k

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
substituteValue ctxt (NecF ty expr) = 
    do ty' <- substitute ctxt ty
       return $ Nec ty' expr
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

    unify' t@(TyInfix o t1 t2) t'@(TyInfix o' t1' t2') | o == o' = do
      u1 <- unify' t1 t1'
      u2 <- unify' t2 t2'
      lift $ combineSubstitutionsHere u1 u2

      {-
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
            -}

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
          let subst = [(tyVar, SubstT k)]
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
