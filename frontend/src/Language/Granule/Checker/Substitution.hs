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
  freshPolymorphicInstance,
  updateTyVar,
  substituteInSignatures) where

import Control.Monad.State.Strict
import Data.Bifunctor.Foldable (bicataM)
import Data.List (elemIndex, sortBy)
import Data.Maybe (mapMaybe)

import Language.Granule.Context

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr hiding (Substitutable)
import Language.Granule.Syntax.Helpers hiding (freshIdentifierBase)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
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

instance {-# OVERLAPPABLE #-} Substitutable t => Substitutable (Ctxt t) where
  substitute subst = mapM (\(v, t) -> substitute subst t >>= (\t' -> return (v, t')))

instance Substitutable t => Substitutable (Maybe t) where
  substitute s Nothing = return Nothing
  substitute s (Just t) = substitute s t >>= return . Just



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

instance Substitutable (Ctxt (Type, Quantifier)) where

  substitute subst ctxt = do
    mapM (\(v, (t, q)) -> substitute subst t >>= (\t' -> return (v, (t', q)))) ctxt


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
  -> Instantiation -- ^ A substitution associated with this type scheme (e.g., for
                  --     data constructors of indexed types) that also needs freshening
  -> [Int]        -- ^ Type Indices if this is a data constructor for an indexed type
  -> Checker (Type, Ctxt Kind, [Type], Substitution)
    -- Returns the type (with new instance variables)
       -- a context of all the instance variables kinds (and the ids they replaced)
       -- a list of the (freshened) constraints for this scheme
       -- a correspondigly freshened version of the parameter substitution
freshPolymorphicInstance quantifier isDataConstructor tyS@(Forall s kinds constr ty) ixSubstitution indices = do

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

    return (tyFreshened, newTyVars, constrFreshened, ixSubstitution')

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
    typesFromIndices (FunTy _ _ _ t) index indices = typesFromIndices t (index+1) indices
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

-- Only applies subsitutions into the kinding signatures
substituteInSignatures :: (?globals :: Globals)
             => Substitution ->  Pred -> Checker Pred
substituteInSignatures subst =
      predFoldM
        (return . Conj)
        (return . Disj)
        (\idks p1 p2 -> do
             -- Apply substitution to id-kind pairs
             idks' <- mapM (\(id, k) -> substitute subst k >>= (\k -> return (id, k))) idks
             return $ Impl idks' p1 p2)
        -- Apply substitution also to the constraint
        (\c -> substituteConstraintHelper substituteIntoTypeSigs subst c >>= (return . Con))
        (return . NegPred)
        -- Apply substitution also to the kinding
        (\id k p -> (substitute subst k) >>= (\k -> return $ Exists id k p))
  where
    substituteIntoTypeSigs subst =
       typeFoldM (baseTypeFold {
        tfTyGrade = (\k i -> do
              k' <- substitute subst k
              mTyGrade k' i)
      , tfTySig = \t _ k -> do
         substitute subst k >>= (\k' -> mTySig t k' k')  })

substituteConstraintHelper :: (?globals::Globals) =>
  (Substitution -> Type -> Checker Type)
  -> Substitution -> Constraint -> Checker Constraint
substituteConstraintHelper substType ctxt (Eq s c1 c2 k) = do
  c1 <- substType ctxt c1
  c2 <- substType ctxt c2
  k <- substType ctxt k
  return $ Eq s c1 c2 k

substituteConstraintHelper substType ctxt (Neq s c1 c2 k) = do
  c1 <- substType ctxt c1
  c2 <- substType ctxt c2
  k <- substitute ctxt k
  return $ Neq s c1 c2 k

substituteConstraintHelper substType ctxt (Lub s c1 c2 c3 k) = do
  c1 <- substType ctxt c1
  c2 <- substType ctxt c2
  c3 <- substType ctxt c3
  k <- substitute ctxt k
  return $ Lub s c1 c2 c3 k

substituteConstraintHelper substType ctxt (ApproximatedBy s c1 c2 k) = do
  c1 <- substType ctxt c1
  c2 <- substType ctxt c2
  k <- substitute ctxt k
  return $ ApproximatedBy s c1 c2 k

substituteConstraintHelper substType ctxt (Lt s c1 c2) = do
  c1 <- substType ctxt c1
  c2 <- substType ctxt c2
  return $ Lt s c1 c2

substituteConstraintHelper substType ctxt (Gt s c1 c2) = do
  c1 <- substType ctxt c1
  c2 <- substType ctxt c2
  return $ Gt s c1 c2

substituteConstraintHelper substType ctxt (LtEq s c1 c2) = LtEq s <$> substType ctxt c1 <*> substType ctxt c2
substituteConstraintHelper substType ctxt (GtEq s c1 c2) = GtEq s <$> substType ctxt c1 <*> substType ctxt c2

substituteConstraintHelper substType ctxt (Hsup s c1 c2 k) = do
  c1 <- substType ctxt c1
  c2 <- substType ctxt c2
  k <- substitute ctxt k
  return $ Hsup s c1 c2 k

instance Substitutable Constraint where
  substitute = substituteConstraintHelper substitute

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
