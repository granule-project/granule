{- |
Module      :  Language.Granule.Checker.Rewrite
Description :  Rewrite a type-annotated AST to an intermediate representation

Rewrites a type-annotated AST to an intermediate representation
without interfaces.
-}


{-# LANGUAGE ImplicitParams #-}
module Language.Granule.Checker.Rewrite
    ( rewriteWithoutInterfaces

      -- ** Annotation helpers
    , mapAnnotations
    , forgetAnnotations
    ) where


import Control.Arrow ((***), (&&&))
import Control.Monad (join)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (evalState)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Data.Function (on)
import Data.List (foldl', groupBy, nub, sortBy)
import Data.Maybe (fromMaybe)

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Helpers (freeVars)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Type

import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Utils

import qualified Language.Granule.Checker.Monad as C
import qualified Language.Granule.Checker.Substitutions as Sub

import Language.Granule.Checker.Rewrite.Type


-- | Return a unique (in scope) variable representing the interface
-- | dictionary at the given type.
mkDictVar :: (?globals :: Globals) => Id -> Type -> Id
mkDictVar name ty = mkId $ "$" <> pretty name <> "(" <> pretty ty <> ")"


-- | Return a unique (in scope) variable representing the interface
-- | dictionary at the given type.
mkDictVarFromCon :: (?globals :: Globals) => Type -> Id
mkDictVarFromCon (TyApp (TyCon iname) ty) = mkDictVar iname ty
mkDictVarFromCon t = error $ "attempt to make a dict var from type: " <> pretty t


-- | Generate a fresh dictionary variable for an instance.
freshDictName :: (?globals :: Globals) => Id -> IFaceDat -> Id
freshDictName name (IFaceDat _ ty) = mkDictVar name ty


-- | Get the name of the dictionary type constructor for the interface.
getDictTyCon :: (?globals :: Globals) => Id -> Type
getDictTyCon n = TyCon n


-- | Get the id of the data constructor for the interface.
ifaceConId :: (?globals :: Globals) => Id -> Id
ifaceConId = mkId . ("$Mk"<>) . pretty


-- | Get the data constructor for the interface.
ifaceDataCon :: (?globals :: Globals) => Id -> Expr v ()
ifaceDataCon n = Val nullSpanNoFile () $ Constr () (ifaceConId n) []


------------------------------
----- Annotation Helpers -----
------------------------------


-- | Forget the AST's annotations.
forgetAnnotations :: AST v a -> AST v ()
forgetAnnotations = mapAnnotations (const ())


-- | Map over an AST's annotations.
mapAnnotations :: (a -> b) -> AST v a -> AST v b
mapAnnotations f (AST dds defs ifaces insts) =
    AST dds    (fmap (mapDefAnnotation f)      defs)
        ifaces (fmap (mapInstanceAnnotation f) insts)


mapInstanceAnnotation :: (a -> b) -> Instance v a -> Instance v b
mapInstanceAnnotation f (Instance s n constrs idat idefs) =
    Instance s n constrs idat (fmap (mapIDefAnnotation f) idefs)


mapIDefAnnotation :: (a -> b) -> IDef v a -> IDef v b
mapIDefAnnotation f (IDef s n eq) = IDef s n (mapEquationAnnotation f eq)


mapDefAnnotation :: (a -> b) -> Def v a -> Def v b
mapDefAnnotation f (Def s n eqs tys) = Def s n (fmap (mapEquationAnnotation f) eqs) tys


mapEquationAnnotation :: (a -> b) -> Equation v a -> Equation v b
mapEquationAnnotation f (Equation s ann pats expr) =
    Equation s (f ann) (fmap (mapPatternAnnotation f) pats) (mapExprAnnotation f expr)


mapExprAnnotation :: (a -> b) -> Expr v a -> Expr v b
mapExprAnnotation f (App s ann e1 e2) =
    App s (f ann) (mapExprAnnotation f e1) (mapExprAnnotation f e2)
mapExprAnnotation f (Binop s ann op l r) =
    Binop s (f ann) op (mapExprAnnotation f l) (mapExprAnnotation f r)
mapExprAnnotation f (LetDiamond s ann pat mty e1 e2) =
    LetDiamond s (f ann) (mapPatternAnnotation f pat) mty (mapExprAnnotation f e1) (mapExprAnnotation f e2)
mapExprAnnotation f (Val s ann v) = Val s (f ann) (mapValueAnnotation f v)
mapExprAnnotation f (Case s ann sw ar) =
    Case s (f ann) (mapExprAnnotation f sw) (fmap (mapPatternAnnotation f *** mapExprAnnotation f) ar)


mapValueAnnotation :: (a -> b) -> Value v a -> Value v b
mapValueAnnotation f (Abs ann pat t expr) =
    Abs (f ann) (mapPatternAnnotation f pat) t (mapExprAnnotation f expr)
mapValueAnnotation f (Promote ann expr) =
    Promote (f ann) (mapExprAnnotation f expr)
mapValueAnnotation f (Pure ann expr) =
    Pure (f ann) (mapExprAnnotation f expr)
mapValueAnnotation f (Constr ann n vs) =
    Constr (f ann) n (fmap (mapValueAnnotation f) vs)
mapValueAnnotation f (Var ann n) = Var (f ann) n
mapValueAnnotation _ (NumInt n) = NumInt n
mapValueAnnotation _ (NumFloat n) = NumFloat n
mapValueAnnotation _ (CharLiteral c) = CharLiteral c
mapValueAnnotation _ (StringLiteral s) = StringLiteral s
mapValueAnnotation f (Ext ann extv) = Ext (f ann) extv


mapPatternAnnotation :: (a -> b) -> Pattern a -> Pattern b
mapPatternAnnotation f (PVar    s ann n)   = PVar s (f ann) n
mapPatternAnnotation f (PWild   s ann)     = PWild s (f ann)
mapPatternAnnotation f (PBox    s ann pat) = PBox s (f ann) (mapPatternAnnotation f pat)
mapPatternAnnotation f (PInt    s ann v)   = PInt s (f ann) v
mapPatternAnnotation f (PFloat  s ann v)   = PFloat s (f ann) v
mapPatternAnnotation f (PConstr s ann n pats) =
    PConstr s (f ann) n (fmap (mapPatternAnnotation f) pats)


--------------------------------------------
----- Helpers for working with Checker -----
--------------------------------------------


-- TODO: remove use of unsafePerformIO (perhaps have the Checker Monad
-- switch to use MonadIO, or the Rewriter could use MonadIO and use liftIO)
runMaybeTCheckerInRewriter :: MaybeT C.Checker a -> Rewriter (Maybe a)
runMaybeTCheckerInRewriter =
  liftIO . C.evalChecker C.initState . runMaybeT


------------------------
----- AST Rewriter -----
------------------------


type ValueRW v = Value v ()
type ExprRW  v = Expr  v ()
type PatternRW = Pattern ()
type DefRW v = Def () ()


-- | Rewrite a type-annotated AST to an intermediate
-- | representation without interfaces.
rewriteWithoutInterfaces :: (?globals :: Globals) => RewriteEnv -> AST () Type -> IO (Either RewriterError (AST () ()))
rewriteWithoutInterfaces renv ast =
    let (AST dds defs ifaces insts) = ast
    in runNewRewriter (do
      ifaces' <- mapM mkIFace ifaces
      instsToDefs <- mapM mkInst insts
      defs' <- mapM rewriteDef defs
      let ifaceDDS = fmap fst ifaces'
          ifaceDefs = concat $ fmap snd ifaces'
      pure $ AST (dds <> ifaceDDS) (ifaceDefs <> instsToDefs <> defs') [] []) renv


-- | Rewrite an interface to its intermediate representation.
--
-- @
--   interface {Foo a} => Bar a where
--     bar1 : a -> a
--     bar2 : a
-- @
--
-- becomes:
--
-- @
--   data Bar a = MkBar ((Foo a) []) ((a -> a) []) (a [])
--
--   barToFoo : forall {a : Type} . Bar a -> Foo a
--   barToFoo (MkBar [d] [_] [_]) = d
--
--   bar1 : forall {a : Type} . Bar a -> a -> a
--   bar1 (MkBar [_] [m] [_]) = f
--
--   bar2 : forall {a : Type} . Bar a -> a
--   bar2 (MkBar [_] [_] [m]) = m
-- @
mkIFace :: (?globals :: Globals) => IFace -> Rewriter (DataDecl, [Def v ()])
mkIFace (IFace sp iname _constrs kind pname itys) = do
    let numMethods = length itys
        dname = ifaceConId iname
        dcon = case collectMethodBindings itys of
                 [] -> DataConstrNonIndexed sp dname typs
                 binds -> DataConstrIndexed sp dname
                   (mkSig binds . mkFunFap1 $ typs <> [dty])
        ddcl = DataDecl sp iname [(pname, fromMaybe KType kind)] Nothing [dcon]
        typs = let typs1 = fmap (ityName &&& ityToTy) itys
               in fmap snd $ sortBy (compare `on` fst) typs1
        defs = fmap ityToDef (zip (sortBy (compare `on` ityName) itys) [1..])
        dty = TyApp (TyCon iname) (TyVar pname)
        matchVar = mkId "$match"
        mkPat i =
            let wildMatches = replicate numMethods
                              (mkBoxedPat (PWild nullSpanNoFile ()))
                (wbefore, wafter) = splitAt i wildMatches
                pats = tail wbefore <> [mkBoxedVar matchVar] <> wafter
            in PConstr nullSpanNoFile () dname pats
        ityToDef ((IFaceTy sp' n (Forall _ q c ty)), i) =
            let binds = nub $ q <> fmap (\v -> (v, KType)) (freeVars ty')
                ty' = FunTy dty ty
            in Def sp' n [Equation sp' () [mkPat i]
                                       (Val sp' () (Var () matchVar))]
                   (Forall sp' binds c ty')
    mapM_ registerDef defs
    registerInterface iname
    pure (ddcl, defs)
    where ityToTy (IFaceTy _ _ (Forall _ _ _ ty)) = Box (CInterval (CNat 0) (CNat 1)) ty;
          ityName (IFaceTy _ n _) = n
          mkBoxedVar = mkBoxedPat . PVar nullSpanNoFile ()
          ityBinds (IFaceTy _ _ (Forall _ binds _ _)) = binds
          collectMethodBindings = nub . foldr (<>) [] . fmap ityBinds


-- | Rewrite an instance to its intermediate representation.
--
-- @
--   instance Bar A where
--     bar1 Av = Av
--     bar2 = Av
-- @
--
-- becomes:
--
-- @
--   barA : Bar A
--   barA = MkBar [fooA] [\Av -> Av] [Av]
-- @
mkInst :: (?globals :: Globals) => Instance () Type -> Rewriter (Def () ())
mkInst inst@(Instance sp iname iconstrs idt@(IFaceDat _ ty) _) = do
    idictConstructed <- constructIDict inst
    let iconstrs' = fmap mkInfBoxTy iconstrs
    pats <- rewriteWithConstrPats iconstrs' []
    let dictName = freshDictName iname idt
        idictTyCon = getDictTyCon iname
        constrsTys = mkFunFap (TyApp idictTyCon ty) iconstrs'
        binds = fmap (\v -> (v, KType)) (nub $ freeVars constrsTys)
        tys = Forall sp binds [] constrsTys
        eqn = Equation sp () pats idictConstructed
        def = Def sp dictName [eqn] tys
    registerIFun iname ty def
    pure def


getInstanceGrouped :: Instance v a -> Rewriter [(Id, TypeScheme, [Equation v a])]
getInstanceGrouped inst@(Instance _ _ _ _ ds) = do
  let nameGroupedDefs = groupBy
        (\(IDef _ name1 _) (IDef _ name2 _) ->
          name1 == name2 || name2 == Nothing) ds
      groupedEqns = sortBy (compare `on` fst) $ map
        (\((IDef _ (Just name) eq):dt) ->
          let eqs = map (\(IDef _ _ eqn) -> eqn) dt
          in (name, eq:eqs)) nameGroupedDefs
  mapM (\(name, eqns) -> do
          ty <- getInstanceMethTys (mkInstanceId inst) name
          pure (name, ty, eqns)) groupedEqns


-- | Construct an expression that builds an appropriate dictionary
-- | instance for the interface.
constructIDict :: (?globals :: Globals) => Instance () Type -> Rewriter (ExprRW ())
constructIDict inst@(Instance _ iname _ _ _) = do
  grouped <- getInstanceGrouped inst
  lambdas <- mapM desugarIdef grouped
  pure $ mkFap (ifaceDataCon iname) lambdas
    where
      desugarIdef (n, t, eqns) = do
        (t', constrs) <- rewriteTypeScheme n t False
        eqns' <- mapM (rewriteEquation constrs) eqns
        pure $ boxExpr (desugar eqns' t')


-- | Produce a lambda expression from a set of equations and a typescheme.
desugar :: [Equation v ()] -> TypeScheme -> ExprRW v
desugar eqs (Forall _ _ _ ty) =
  typeDirectedDesugarEquation mkSingleEquation
  where
    typeDirectedDesugarEquation (Equation _ _ ps body) =
        -- Desugar the body
        (evalState (typeDirectedDesugar ps body ty) (0 :: Int))

    typeDirectedDesugar [] e _ = return e
    typeDirectedDesugar (p : ps) e (FunTy t1 t2) = do
      e' <- typeDirectedDesugar ps e t2
      return $ Val nullSpanNoFile () $ Abs () p (Just t1) e'
    typeDirectedDesugar _ _ _ = error "internal error: Rewriter.desugar"
    -- Fold function equations into a single case expression
    mkSingleEquation =
      Equation nullSpanNoFile () (map (PVar nullSpanNoFile ()) vars) rhs

      where
        rhs = if numArgs == 0
              -- when we have no arguments we can just reuse the (sole)
              -- RHS expression
              then let [Equation _ _ _ expr] = eqs in expr
              -- otherwise we make a case expression to cover all of the
              -- patterns
              else
                  let -- Guard expression
                      guard = foldl1 (pair nullSpanNoFile) guardVars
                      guardVars = map (\i -> Val nullSpanNoFile () (Var () i)) vars

                      -- case for each equation
                      cases = map (\(Equation _ _ pats expr) ->
                        (foldl1 (ppair nullSpanNoFile) pats, expr)) eqs
                  in (Case nullSpanNoFile () guard cases)

        numArgs = case head eqs of Equation _ _ ps _ -> length ps
        -- List of variables to represent each argument
        vars = [mkId ("$internal" ++ show i) | i <- [1..numArgs]]



rewriteDef :: (?globals :: Globals) => Def () Type -> Rewriter (DefRW ())
rewriteDef (Def sp n eqns tys) = do
  (tys', cts) <- rewriteTypeScheme n tys True
  eqns' <- mapM (rewriteEquation cts) eqns
  let newDef = Def sp n eqns' tys'
  registerDef newDef
  pure newDef


rewriteWithConstrPats :: (?globals :: Globals) => [Type] -> [Pattern a] -> Rewriter [Pattern ()]
rewriteWithConstrPats ts pats = do
    pats' <- mapM rewritePattern pats
    pure $ constrPats <> pats'
    where constrPats = fmap mkVpat ts
          mkVpat (Box _ t) = mkBoxedPat $ mkVpat t
          mkVpat t = PVar nullSpanNoFile () (mkDictVarFromCon t)


rewriteEquation :: (?globals :: Globals) => [Type] -> Equation v Type -> Rewriter (Equation v ())
rewriteEquation ts (Equation sp _ pats expr) = do
    expr' <- rewriteExpr expr
    pats' <- rewriteWithConstrPats ts pats
    pure $ Equation sp () pats' expr'


rewriteExpr :: (?globals :: Globals) => Expr v Type -> Rewriter (ExprRW v)
rewriteExpr (App s _ e1 e2) = do
  e1' <- rewriteExpr e1
  e2' <- rewriteExpr e2
  pure $ App s () e1' e2'
rewriteExpr (Binop s _ op l r) = do
  l' <- rewriteExpr l
  r' <- rewriteExpr r
  pure $ Binop s () op l' r'
rewriteExpr (LetDiamond s _ pat mty e1 e2) = do
  pat' <- rewritePattern pat
  e1' <- rewriteExpr e1
  e2' <- rewriteExpr e2
  pure $ LetDiamond s () pat' mty e1' e2'
rewriteExpr (Val s ann v@(Var _ n)) = do
  v' <- rewriteValue v
  maybeDef <- lookupDef n
  case maybeDef of
    Just def -> rewriteDefCall def ann
    Nothing -> pure $ Val s () v'
rewriteExpr (Val s _ v) = fmap (Val s ()) $ rewriteValue v
rewriteExpr (Case s _ sw ar) = do
  sw' <- rewriteExpr sw
  ar' <- mapM rewriteAr ar
  pure $ Case s () sw' ar'
    where rewriteAr (p,e) = do
            p' <- rewritePattern p
            e' <- rewriteExpr e
            pure (p', e')


rewriteDefCall :: (?globals :: Globals) => Def () () -> Type -> Rewriter (Expr v ())
rewriteDefCall (Def _ n _ tys) callTy = do
  (Forall _ _ _ ty) <- instantiate tys callTy
  dictArgs <- dictArgsFromTy ty
  pure $ mkFap (Val nullSpanNoFile () $ Var () n) dictArgs


-- | Instantiate the typescheme with the given type.
-- | The typescheme should already have interface constraints rewritten as types.
-- |
-- | This will fail if the typescheme cannot be instantiated with the given type.
instantiate :: (?globals :: Globals) => TypeScheme -> Type -> Rewriter TypeScheme
instantiate sig@(Forall _ _ _ ty) ity = do
  tyNoI <- rewriteTypeWithoutInterfaces ty
  res <- runMaybeTCheckerInRewriter $ do
           subst <- Sub.unify tyNoI ity
           maybe (pure sig) (`Sub.substitute` sig) subst
  maybe (genericRewriterError $ concat ["error when instantiating '", pretty sig, "' with '", pretty ity, "'"]) pure res
  where rewriteTypeWithoutInterfaces ta@(FunTy t1 t2) = do
            isIface <- maybe False (const True) <$> extractIFaceTy t1
            if isIface then rewriteTypeWithoutInterfaces t2 else pure ta
        rewriteTypeWithoutInterfaces t = pure t


-- | Convert a type to a list of dictionary expressions to apply to the
-- | associated expression.
dictArgsFromTy :: (?globals :: Globals) => Type -> Rewriter [Expr v ()]
dictArgsFromTy (FunTy t ts) = do
    iface <- extractIFaceTy t
    case iface of
      Nothing -> pure []
      Just (isBoxed, iname, ity) -> do
        dexp <- (do
             d <- getConcreteInstExpr iname ity
             -- we must assume that the arg comes from a passed
             -- argument if the result is 'Nothing'
             let dname = mkDictVar iname ity
             pure . (if isBoxed then boxExpr else id)
                      $ fromMaybe (mkVarExpr dname) d)
        fmap (dexp:) (dictArgsFromTy ts)
dictArgsFromTy _ = pure []


getConcreteInstExpr :: (?globals :: Globals) => Id -> Type -> Rewriter (Maybe (Expr v ()))
getConcreteInstExpr iname ity = do
    instFun <- lookupFirstInstFun iname ity
    maybe (pure Nothing) (fmap Just . extractInstFun) instFun
    where extractInstFun (Concrete dname) =
            pure $ Val nullSpanNoFile () (Var () dname)
          extractInstFun (Constrained n ty) = do
            dictArgs <- dictArgsFromTy ty
            pure $ mkFap (Val nullSpanNoFile () $ Var () n) dictArgs


-- | An instance of an interface dictionary is either concrete, or
-- | is constrained by the given type.
data IDictFun = Concrete Id | Constrained Id Type


lookupFirstInstFun :: (?globals :: Globals) => Id -> Type -> Rewriter (Maybe IDictFun)
-- TODO: add support for fully polymorphic instances (GuiltyDolphin - 2019-03-03)
lookupFirstInstFun _ (TyVar _) = pure Nothing
lookupFirstInstFun iname ty = do
  instFuns <- lookupIfaceIfuns iname
  maybe (pure Nothing) firstUnifyingFun instFuns
  where firstUnifyingFun [] = pure Nothing
        firstUnifyingFun ((t, (Def _ dname _ dtys)):xs) = do
            if (t == ty) then pure . Just $ Concrete dname
            else do
              unif <- fmap join $ runMaybeTCheckerInRewriter (Sub.unify t ty)
              maybe (firstUnifyingFun xs) (\sbst -> do
                maybeDTys <- runMaybeTCheckerInRewriter (Sub.substitute sbst dtys)
                pure $ fmap (\(Forall _ _ _ dty) -> Constrained dname dty) maybeDTys) unif


rewritePattern :: Pattern a -> Rewriter PatternRW
rewritePattern (PBox s _ pat)       = fmap (PBox    s ())   $ rewritePattern pat
rewritePattern (PConstr s _ n pats) = fmap (PConstr s () n) $ mapM rewritePattern pats
rewritePattern p = pure . mapPatternAnnotation (const ())   $ p


rewriteValue :: (?globals :: Globals) => Value v Type -> Rewriter (ValueRW v)
rewriteValue (Abs _ pat t expr) = do
  pat'  <- rewritePattern pat
  expr' <- rewriteExpr expr
  pure $ Abs () pat' t expr'
rewriteValue (Promote _ expr) = fmap (Promote ())  $ rewriteExpr expr
rewriteValue (Pure    _ expr) = fmap (Pure ())     $ rewriteExpr expr
rewriteValue (Constr  _ n vs) = fmap (Constr () n) $ mapM rewriteValue vs
rewriteValue v = pure . mapValueAnnotation (const ()) $ v


-- | Rewrite a typescheme without interface constraints.
-- |
-- | Interface constraints simply become standard types.
rewriteTypeScheme :: Id -> TypeScheme -> Bool -> Rewriter (TypeScheme, [Type])
rewriteTypeScheme n (Forall sp binds cts ty) doExpand = do
  constrs <- if doExpand then fmap (fmap mkInfBoxTy) (expandConstraints n) else pure cts
  let funty = mkFunFap ty constrs
  pure (Forall sp binds [] funty, constrs)


---------------------
----- Utilities -----
---------------------


mkFap :: Expr v () -> [Expr v ()] -> Expr v ()
mkFap = foldl' (App nullSpanNoFile ())


mkFunFap :: Type -> [Type] -> Type
mkFunFap ty = foldr FunTy ty


mkFunFap1 :: [Type] -> Type
mkFunFap1 tys = foldr1 FunTy tys


mkVar :: Id -> Value v ()
mkVar = Var ()


mkVal :: Value v () -> Expr v ()
mkVal = Val nullSpanNoFile ()


mkVarExpr :: Id -> Expr v ()
mkVarExpr = mkVal . mkVar


mkBoxedPat :: Pattern () -> Pattern ()
mkBoxedPat = PBox nullSpanNoFile ()


boxExpr :: Expr v () -> Expr v ()
boxExpr = Val nullSpanNoFile () . Promote ()


mkInfBoxTy :: Type -> Type
mkInfBoxTy = Box (CInterval (CZero extendedNat) infinity)


-- | Create a typescheme supported by the intermediate language.
-- |
-- | This is the same as a regular typescheme, but without support
-- | for constraints.
mkSig :: [(Id, Kind)] -> Type -> TypeScheme
mkSig binds ty = Forall nullSpanNoFile binds [] ty
-- TODO: make sure this plays well with predicate constraints
--       (GuiltyDolphin - 2019-03-07)


-- | Attempt to extract interface information from the type.
-- |
-- | Returns (isBoxed, name, instTy) if successful, Nothing otherwise.
extractIFaceTy :: Type -> Rewriter (Maybe (Bool, Id, Type))
extractIFaceTy (Box _ t) =
    fmap (fmap (\(_,n,ty) -> (True, n, ty))) $ extractIFaceTy t
extractIFaceTy (TyApp (TyCon n) ty) = do
    isIface <- isInterfaceVar n
    pure $ if isIface then Just (False, n, ty) else Nothing
extractIFaceTy _ = pure Nothing
