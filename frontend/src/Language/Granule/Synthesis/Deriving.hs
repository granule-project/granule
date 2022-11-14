module Language.Granule.Synthesis.Deriving
  (derivePush, derivePull, deriveCopyShape, deriveDrop) where

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Span
import Language.Granule.Context

import Language.Granule.Checker.Predicates (Constraint(..))
import Language.Granule.Checker.Kinding
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates (Quantifier(..))
import Language.Granule.Checker.Types (SpecIndicator(..), equalTypesRelatedCoeffectsAndUnify)
import Language.Granule.Checker.Variables
import Language.Granule.Checker.SubstitutionContexts

import Language.Granule.Synthesis.Builders

import Language.Granule.Utils
--import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Strict (modify, get)
import Control.Monad (zipWithM, forM)

  {-
  Module for automatically deriving graded linear logical
  operations based on types.
  -}

derivePush :: (?globals :: Globals) => Span -> Type -> Checker (TypeScheme, Def () ())
derivePush s ty = do
  -- Create fresh variables for the grades
  kVar <- freshIdentifierBase "k" >>= (return . mkId)
  cVar <- freshIdentifierBase "r" >>= (return . mkId)

  -- Get kind of type constructor
  (kind, _, _) <- synthKind nullSpanNoFile ty
  -- Generate fresh type variables and apply them to the kind constructor
  (localTyVarContext, baseTy, returnTy') <- fullyApplyType kind (TyVar cVar) ty
  let tyVars = map (\(id, (t, _)) -> (id, t)) localTyVarContext
  let argTy = Box (TyVar cVar) baseTy

  -- For the purposes of recursive types, temporarily 'register' a dummy
  -- definition for this push
  st0 <- get
  modify (\st -> st { derivedDefinitions =
                        ((mkId "push", ty), (trivialScheme $ FunTy Nothing Nothing argTy returnTy', undefined))
                         : derivedDefinitions st
                    , tyVarContext = tyVarContext st ++ [(kVar, (kcoeffect, ForallQ)), (cVar, (TyVar kVar, ForallQ))] ++ localTyVarContext })

  -- Give a name to the input
  z <- freshIdentifierBase "z" >>= (return . mkId)
  (returnTy, bodyExpr, isPoly) <-
    derivePush' s True (TyVar cVar) [] tyVars baseTy (makeVarUntyped z)

  -- Build derived type scheme
  let constraints =
        if isPoly
          then [TyInfix TyOpLesserEq (TyGrade (Just (TyVar kVar)) 1) (TyVar cVar)]
          else []
  let tyS = Forall s
              ([(kVar, kcoeffect), (cVar, (TyVar kVar))] ++ tyVars)
              constraints
              (FunTy Nothing Nothing argTy returnTy)
  -- Build the expression
  let expr = Val s () True $ Abs () (PVar s () True z) Nothing bodyExpr
  let name = mkId $ "push@" ++ pretty ty

  -- Remove the dummy definition here
  modify (\st -> st { derivedDefinitions = deleteVar' (mkId "push", ty) (derivedDefinitions st)
                    -- Restore type variables and predicate stack
                    , tyVarContext = tyVarContext st0
                    , predicateStack = predicateStack st0 } )
  return $
    (tyS, Def s name True Nothing
            (EquationList s name True
               [Equation s name () True [] expr]) tyS)

-- derivePush' does the main work.
-- For example, if we are deriving for the type constructor F
-- then we want to compute:  [] r (F a1 .. an) -> F ([] r a1) .. ([] r an)
-- It takes as parameters:
--   * the grade used to annotate the graded modality: `r`
--   * the context of recursion variables: Sigma
--   * the context of type variables used to instantiate this: a1...an
--   * the type from which we are deriving: F a1...an
--   * the argument expression of type [] r (F a1 .. an)
-- It returns:
--   * the return type: F ([] r a1) .. ([] r an)
--   * the and the expression of this type
--   * whether this is polyshaped or not
derivePush' :: (?globals :: Globals)
            => Span
            -> Bool
            -> Type -> Ctxt Id -> Ctxt Kind -> Type -> Expr () () -> Checker (Type, Expr () (), Bool)

-- Type variable case: push_alpha arg = arg
derivePush' topLevel s c _sigma gamma argTy@(TyVar n) arg = do
  case lookup n gamma of
    Just _ -> return (Box c argTy, arg, False)
    Nothing -> do
      -- For arguments which are type variables but not parameters
      -- to this type constructor, then we need to do an unboxing
      x <- freshIdentifierBase "x" >>= (return . mkId)
      let expr = makeUnboxUntyped x arg (makeVarUntyped x)
      return (argTy, expr, False)

-- Unit case:  push_() arg = (case arg of () -> ()) : ())
derivePush' s topLevel c _sigma gamma argTy@(TyCon (internalName -> "()")) arg = do
  let ty  = argTy
  return (ty, makeUnitElimPUntyped pbox arg makeUnitIntroUntyped, False)

-- Pair case: push_(t1,t2) arg = (case arg of (x, y) -> (push_t1 [x], push_t2 [y])
derivePush' s topLevel c _sigma gamma argTy@(ProdTy t1 t2) arg = do
  x <- freshIdentifierBase "x" >>= (return . mkId)
  y <- freshIdentifierBase "y" >>= (return . mkId)
  -- Induction
  (leftTy, leftExpr, lisPoly)   <- derivePush' s topLevel c _sigma gamma t1 (makeBoxUntyped (makeVarUntyped x))
  (rightTy, rightExpr, risPoly) <- derivePush' s topLevel c _sigma gamma t2 (makeBoxUntyped (makeVarUntyped y))
  -- Build eliminator
  let returnTy = ProdTy leftTy rightTy
  return (returnTy, makePairElimPUntyped pbox arg x y
                     (makePairUntyped leftExpr rightExpr), lisPoly || risPoly)

-- General type constructor case:
derivePush' s topLevel c _sigma gamma argTy@(leftmostOfApplication -> TyCon name) arg = do
  -- First check whether this has already been derived or not
  -- (also deals with recursive types)
  st <- get
  alreadyDefined <-
    if topLevel
      then return Nothing
      else
        case lookup (mkId "push", TyCon name) (derivedDefinitions st) of
          -- We have it in context, so now we need to apply its type
          Just (tyScheme, _) -> do
            -- freshen the type
            (pushTy, _, _, _constraints, _) <- freshPolymorphicInstance InstanceQ False tyScheme []
            case pushTy of
              t@(FunTy _ _ t1 t2) -> do
                  -- Its argument must be unified with argTy here
                  debugM "derive-push" ("eq on argTy = " <> pretty (Box c argTy) <> " t1 = " <> pretty t1)
                  (eq, tRes, subst) <- equalTypesRelatedCoeffectsAndUnify s Eq FstIsSpec (Box c argTy) t1
                  if eq
                    -- Success!
                    then do
                      t2' <- substitute subst t2
                      return (Just (t2', App s () True (makeVarUntyped (mkId $ "push@" <> pretty name)) arg))
                    else do
                      -- Couldn't do the equality.
                      return Nothing
              _ -> return Nothing
          Nothing -> return Nothing

  case alreadyDefined of
    Just (pushResTy, pushExpr) -> do
      -- still check arity
      mConstructors <- getDataConstructors name
      let isPoly =
            case mConstructors of
               Just xs | length xs > 1 -> True
               _                       -> False
      return (pushResTy, pushExpr, isPoly)
    Nothing ->
      -- Not already defined...
      -- Get the kind of this type constructor
      case lookup name (typeConstructors st) of
        Nothing -> throw UnboundVariableError { errLoc = s, errId = name }
        Just (kind, _, _) -> do

          -- Get all the data constructors of this type
          mConstructors <- getDataConstructors name
          case mConstructors of
            Nothing -> throw UnboundVariableError { errLoc = s, errId = name }
            Just constructors -> do

              -- For each constructor, build a pattern match and an introduction:
              cases <- forM constructors (\(dataConsName, (tySch@(Forall _ _ _ dataConsType), coercions)) -> do

                -- Instantiate the data constructor
                (dataConstructorTypeFresh, freshTyVarsCtxt, freshTyVarSubst, _constraint, coercions') <-
                      freshPolymorphicInstance BoundQ True tySch coercions

                -- [Note: this does not register the constraints associated with the data constrcutor]
                dataConstructorTypeFresh <- substitute (flipSubstitution coercions') dataConstructorTypeFresh

                debugM "deriv-push - dataConstructorTypeFresh" (pretty dataConstructorTypeFresh)
                debugM "deriv-push - eq with" (pretty (resultType dataConstructorTypeFresh) ++ " = " ++ pretty argTy)
                -- Perform an equality between the result type of the data constructor and the argument type here
                areEq <- equalTypesRelatedCoeffectsAndUnify s Eq PatternCtxt (resultType dataConstructorTypeFresh) argTy
                case areEq of
                  -- This creates a unification
                  (False, _, _) ->
                      error $ "Cannot derive push for data constructor " <> pretty dataConsName
                  (True, _, unifiers) -> do
                    debugM "deriv-push areEq" "True"
                    debugM "deriv-push unifiers" (show unifiers)

                    -- Unify and specialise the data constructor type
                    dataConsType <- substitute (flipSubstitution unifiers) dataConstructorTypeFresh
                    debugM "deriv-push dataConsType" (pretty dataConsType)


                    -- Create a variable for each parameter
                    let consParamsTypes = parameterTypes dataConsType
                    consParamsVars <- forM consParamsTypes (\_ -> freshIdentifierBase "y" >>= (return . mkId))

                    -- Build the pattern for this case
                    let consPattern =
                          PConstr s () True dataConsName (zipWith (\ty var -> PVar s () True var) consParamsTypes consParamsVars)
                    let consPatternBoxed =
                          PBox s () True consPattern

                    -- Push on all the parameters of a the constructor
                    retTysAndExprs <- zipWithM (\ty var -> do
                            debugM "derive-push" ("Deriving argument of case for " <> pretty dataConsName <> " at type " <> pretty ty)
                            derivePush' s False c _sigma gamma ty (makeBoxUntyped (makeVarUntyped var)))
                              consParamsTypes consParamsVars
                    let (_retTys, exprs, isPolys) = unzip3 retTysAndExprs

                    let bodyExpr = mkConstructorApplication s dataConsName dataConsType (reverse exprs) dataConsType
                    let isPoly = (length constructors > 1) || or isPolys
                    return ((consPatternBoxed, bodyExpr), isPoly))

              -- Got all the branches to make the following case now
              case objectMappingWithBox argTy kind c of
                Just returnTy -> return (returnTy, Case s () True arg (map fst cases), or (map snd cases))
                Nothing -> error $ "Cannot push derive for type " ++ pretty argTy ++ " due to typing"

derivePush' s _ _ _ _ ty _ = do
  error $ "Cannot push derive for type " ++ pretty ty

-- Based on its type, apply a list of arguments to a ty constructor
mkConstructorApplication :: (?globals :: Globals) => Span -> Id -> Type -> [Expr () ()] -> Type -> Expr () ()
mkConstructorApplication s name consType [] t =
  Val s () True (Constr () name [])

mkConstructorApplication s name consType (expr:exprs) (FunTy _ _ t1 t2) =
  App s () True (mkConstructorApplication s name consType exprs t2) expr

mkConstructorApplication s name consType  exprs ty =
  -- no argument can be applied
  Val s () True (Constr () name [])
  -- error $ "In making constructor for " ++ pretty name ++ " with exprs args " ++ pretty exprs ++ " at type " ++ pretty ty


derivePull :: (?globals :: Globals) => Span -> Type -> Checker (TypeScheme, Def () ())
derivePull s ty = do
  -- Create fresh variables for the grades
  kVar <- freshIdentifierBase "k" >>= (return . mkId)
  cVar <- freshIdentifierBase "r" >>= (return . mkId)

  -- Get kind of type constructor
  (kind, _, _) <- synthKind nullSpanNoFile ty
  -- Generate fresh type variables and apply them to the kind constructor
  (localTyVarContext, baseTy, argTy) <- fullyApplyType kind (TyVar cVar) ty
  let tyVars = map (\(id, (t, _)) -> (id, t)) localTyVarContext

  debugM "pull : " (pretty (FunTy Nothing Nothing argTy (Box (TyVar cVar) baseTy)))
  st0 <- get
  modify (\st -> st {  derivedDefinitions =
                        ((mkId "pull", ty), (trivialScheme $ FunTy Nothing Nothing argTy (Box (TyVar cVar) baseTy), undefined)) : derivedDefinitions st,
                    tyVarContext = tyVarContext st ++ [(kVar, (kcoeffect, ForallQ)), (cVar, (TyVar kVar, ForallQ))] ++ localTyVarContext })

  z <- freshIdentifierBase "z" >>= (return . mkId)
  (returnTy, bodyExpr, coeff) <-
    derivePull' s True tyVars argTy (makeVarUntyped z)

  modify (\st -> st { derivedDefinitions = deleteVar' (mkId "pull", ty) (derivedDefinitions st)
                    -- Restore type variables and predicate stack
                    , tyVarContext = tyVarContext st0
                    , predicateStack = predicateStack st0 } )

  let coeff' = case coeff of
                Just c -> c
                Nothing -> TyVar cVar

  let tyS = Forall s
          ([(kVar, kcoeffect), (cVar, (TyVar kVar))] ++ tyVars)
          []
          (FunTy Nothing Nothing argTy (Box coeff' baseTy))
  let expr = Val s () True $ Abs () (PVar s () True z) Nothing bodyExpr
  let name = mkId $ "pull@" ++ pretty ty

  return $
    (tyS, Def s name True Nothing
        (EquationList s name True
            [Equation s name () True [] expr]) tyS)

derivePull'  :: (?globals :: Globals)
  => Span
  -> Bool
  -- -> Ctxt Id
  -> Ctxt Kind
  -> Type
  -> Expr () ()
  -> Checker (Type, Expr () (), Maybe Type)

derivePull' s topLevel gamma argTy@(Box c t) arg = do
  (returnTy, expr, coeff) <- derivePull' s topLevel gamma t arg
  case coeff of
    Just c' -> return (returnTy, expr, Just $ TyInfix TyOpMeet c c')
    _ -> return (returnTy, expr, Just $ TyInfix TyOpMeet c c)

derivePull' s topLevel gamma argTy@(TyVar n) arg = do
  case lookup n gamma of
    Just _ -> return (argTy, arg, Nothing)
    Nothing -> return (argTy, arg, Nothing)

     -- do
     -- -- For arguments which are type variables but not parameters
     -- -- to this type constructor, then we need to do an unboxing
     -- x <- freshIdentifierBase "x" >>= (return . mkId)
     -- let expr = makeUnboxUntyped x arg (makeVarUntyped x)
     -- return (argTy, expr)

derivePull' s topLevel gamma argTy@(ProdTy t1 t2) arg = do
  x <- freshIdentifierBase "x" >>= (return . mkId)
  y <- freshIdentifierBase "y" >>= (return . mkId)
  -- Induction
  (leftTy, leftExpr, lCoeff)   <- derivePull' s topLevel gamma t1 (makeVarUntyped x)
  (rightTy, rightExpr, rCoeff) <- derivePull' s topLevel gamma t2 (makeVarUntyped y)
--  let coeffs = (singleton c1) `union` (singleton c2) `union` rCoeffs `union` lCoeffs
  let returnTy = (ProdTy leftTy rightTy)
  case (lCoeff, rCoeff) of
    (Just c, Just c') -> return (returnTy, makePairElimPUntyped' pbox arg x y
                     (makeBoxUntyped (makePairUntyped leftExpr rightExpr)), Just $ TyInfix TyOpMeet c c')
    (_, _) -> return (returnTy, makePairElimPUntyped' pbox arg x y
                     (makeBoxUntyped (makePairUntyped leftExpr rightExpr)), Nothing)

-- General type constructor case:
derivePull' s topLevel gamma argTy@(leftmostOfApplication -> TyCon name) arg = do
  debugM "derive-pull" ("TyCon case " <> pretty argTy)
  -- First check whether this has already been derived or not
  -- (also deals with recursive types)
  st <- get
  alreadyDefined <-
    if topLevel
      then return Nothing
      else
        case lookup (mkId "pull", TyCon name) (derivedDefinitions st) of
          -- We have it in context, so now we need to apply its type
          Just (tyScheme, _) -> do
            -- freshen the type
            (pullTy, _, _, _constraints, _) <- freshPolymorphicInstance InstanceQ False tyScheme []
            case pullTy of
              t@(FunTy _ _ t1 t2) -> do
                  -- Its argument must be unified with argTy here
                  --(eq, tRes, subst) <- equalTypesRelatedCoeffectsAndUnify s Eq FstIsSpec (Box c argTy) t1
                  debugM "derive-pull" ("eq on argTy = " <> pretty argTy <> " t1 = " <> pretty t1)
                  (eq, tRes, subst) <- equalTypesRelatedCoeffectsAndUnify s Eq FstIsSpec argTy t1
                  if eq
                    -- Success!
                    then do
                      debugM "derive-pull" "already defined okay"
                      t2' <- substitute subst t2
                      return (Just (t2', App s () True (makeVarUntyped (mkId $ "pull@" <> pretty name)) arg, Nothing))
                    else do
                      -- Couldn't do the equality.
                      debugM "derive-pull" ("no eq for " ++ pretty argTy ++ " and " ++ pretty t1)
                      return Nothing
              _ -> return Nothing
          Nothing -> return Nothing

  case alreadyDefined of
    Just (pullResTy, pullExpr, coeff) -> return (pullResTy, pullExpr, coeff)
    Nothing ->
      -- Not already defined...
      -- Get the kind of this type constructor
      case lookup name (typeConstructors st) of
        Nothing -> throw UnboundVariableError { errLoc = s, errId = name }
        Just (kind, _, _) -> do

          -- Get all the data constructors of this type
          mConstructors <- getDataConstructors name
          case mConstructors of
            Nothing -> throw UnboundVariableError { errLoc = s, errId = name }
            Just constructors -> do

              -- For each constructor, build a pattern match and an introduction:
              cases <- forM constructors (\(dataConsName, (tySch@(Forall _ _ _ ty), coercions)) -> do
                debugM "deriv-pull - coercions" (show coercions)

                -- Instantiate the data constructor
                (dataConstructorTypeFresh, _, _, _constraint, coercions') <-
                      freshPolymorphicInstance BoundQ True tySch coercions

                debugM "deriv-pull - dataConstructorTypeFresh" (pretty dataConstructorTypeFresh)

               -- [Note: this does not register the constraints associated with the data constrcutor]
                dataConstructorTypeFresh <- substitute (flipSubstitution coercions') dataConstructorTypeFresh

                debugM "deriv-pull - dataConstructorTypeFresh" (pretty dataConstructorTypeFresh)
                debugM "deriv-pull - eq with" (pretty (resultType dataConstructorTypeFresh) ++ " = " ++ pretty argTy)
                -- Perform an equality between the result type of the data constructor and the argument type here

                areEq <- equalTypesRelatedCoeffectsAndUnify s Eq PatternCtxt argTy (resultType dataConstructorTypeFresh)
                debugM "deriv-pull areEq" (show areEq)
                case areEq of
                  -- This creates a unification
                  (False, _, _) ->
                      error $ "Cannot derive pull for data constructor " <> pretty dataConsName
                  (True, _, unifiers) -> do
                    -- Unify and specialise the data constructor type
                    dataConsType <- substitute (unifiers) dataConstructorTypeFresh
                    debugM "deriv-pull dataConsType" (pretty dataConsType)
                    debugM "deriv-pull unifiers" (show unifiers)

                    -- Create a variable for each parameter
                    let consParamsTypes = parameterTypes dataConsType

                    debugM "paramterTypes: " (pretty consParamsTypes)
                    consParamsVars <- forM consParamsTypes (\_ -> freshIdentifierBase "y" >>= (return . mkId))
                    debugM "consParamsVars: " (pretty consParamsVars)

                    -- Build the pattern for this case
                    let consPattern =
                          PConstr s () True dataConsName (zipWith (\ty var -> PBox s () True (PVar s () True var)) consParamsTypes consParamsVars)
                    debugM "derive-pull" ("consPattern " <> pretty consPattern )
                    -- Push on all the parameters of a the constructor
                    retTysAndExprs <- zipWithM (\ty var -> do
                      debugM "derive-pull" ("Deriving argument of case for " <> pretty dataConsName <> " at type " <> pretty ty)
                      derivePull' s False gamma ty (makeVarUntyped var))
                                      consParamsTypes consParamsVars
                    let (_retTys, exprs, coeffs) = unzip3 retTysAndExprs
                    let coeffs' = coeffectMeet coeffs
                    debugM "retTys: " (show _retTys)
                    let bodyExpr = mkConstructorApplication s dataConsName dataConsType (reverse exprs) dataConsType
                    let bodyExpr' = (\bExpr -> case coeffs' of
                                             Just c -> makeBoxUntyped bExpr
                                             Nothing -> bExpr)
                                           bodyExpr
                    return (_retTys, consPattern, bodyExpr', coeffs'))

              -- Got all the branches to make the following case now

              -- Construct the return type from the individual return types of each type argument

              let (returnTys, pats, exprs, coeffs) = unzip4 cases

              debugM "coeffs: " (show coeffs)
              debugM "ty: " (show argTy)
              let ty = reconstructTy (concat returnTys) argTy
              let patExprs = zip pats exprs
              debugM "res: " (pretty (Case s () True arg patExprs))
              case coeffs of
                c:cs -> return (ty, Case s () True arg patExprs, c)
                _ -> return (ty, Case s () True arg patExprs, Nothing)

      where

        unzip4 [] = ([], [], [], [])
        unzip4 ((a,b,c,d):xs) = (a:as, b:bs, c:cs, d:ds)
             where (as, bs, cs, ds) = unzip4 xs

        reconstructTy returnTys (Box c ty) =
          if ty `elem` returnTys then
            ty
          else
            Box c (reconstructTy returnTys ty)
        reconstructTy returnTys (TyApp t1 t2) = TyApp (reconstructTy returnTys t1) (reconstructTy returnTys t2)
        reconstructTy returnTys (FunTy s mCoeff t1 t2) = FunTy s mCoeff (reconstructTy returnTys t1) (reconstructTy returnTys t2)
        reconstructTy _ ty = ty

        coeffectMeet (Just c:[]) = Just c
        coeffectMeet (Just c:cs) = do
          c' <- coeffectMeet cs
          return $ TyInfix TyOpMeet c c'
        coeffectMeet _ = Nothing


  -- Build eliminator

derivePull' _ _ _ ty _ = error $ "still to come!" <> show ty



-- Given a kind for a type constructor, fully apply the type constructor
-- generator with fresh type variables for each parameter and return a type-variable
-- context containing these variables as well as the applied type along with
-- a pair of the applied type (e.g., F a b) [called the base type]
-- and the type for argument of a pull (e.g., F ([] r a) ([] r b))
fullyApplyType :: (?globals :: Globals)
                   => Kind -> Type -> Type -> Checker (Ctxt (Kind, Quantifier), Type, Type)
fullyApplyType k r t = fullyApplyType' k r t t

fullyApplyType' :: (?globals :: Globals)
                    => Kind -> Type -> Type -> Type -> Checker (Ctxt (Kind, Quantifier), Type, Type)
fullyApplyType' (Type _) r baseTy argTy =
  return ([], baseTy, argTy)

fullyApplyType' (FunTy _ _ t1 t2) r baseTy argTy = do
  -- Fresh ty variable
  tyVar <- freshIdentifierBase "a" >>= (return . mkId)
  -- Apply to the base type
  let baseTy' = TyApp baseTy (TyVar tyVar)
  -- Apply to the "argument of push" type
  let argTy'  =
       case t1 of
         (Type _) -> TyApp argTy (Box r (TyVar tyVar))
         _     -> TyApp argTy (TyVar tyVar)
  -- Induction
  (ids, baseTy'', argTy'') <- fullyApplyType' t2 r baseTy' argTy'
  return ((tyVar, (t1, ForallQ)) : ids, baseTy'', argTy'')

fullyApplyType' k _ _ _ =
  error $ "Cannot fully apply for kind " ++ pretty k

-- | e.g. given type `F a b` and kind `F : Type -> Nat -> Type`
-- | this returns the type `F ([] r a) b`
-- | TODO: generalise this to check this only being applied to
-- | type parameters
objectMappingWithBox :: (?globals :: Globals)
                   => Type -> Kind -> Type -> Maybe Type
objectMappingWithBox t k r = objectMappingWithBox' t (reverse $ parameterTypes k) r

objectMappingWithBox' :: (?globals :: Globals)
                    => Type -> [Kind] -> Type -> Maybe Type

objectMappingWithBox' t [] _ = return t

objectMappingWithBox' (TyApp t1 t2) (k:ks) r = do
  t <- objectMappingWithBox' t1 ks r
  case k of
    -- Only added boxes on types
    (Type _)
          -> return $ TyApp t (Box r t2)
    _     -> return $ TyApp t t2

objectMappingWithBox' _ _ _ = Nothing

deleteVar' :: Eq a => a -> [(a, t)] -> [(a, t)]
deleteVar' _ [] = []
deleteVar' x ((y, b) : m) | x == y = deleteVar' x m
                          | otherwise = (y, b) : deleteVar' x m



deriveCopyShape :: (?globals :: Globals) => Span -> Type -> Checker (TypeScheme, Maybe (Def () ()))
deriveCopyShape s ty = do

  -- Create fresh variables for the grades
  kVar <- freshIdentifierBase "k" >>= (return . mkId)
  cVar <- freshIdentifierBase "r" >>= (return . mkId)

  -- Get kind of type constructor
  (kind, _, _) <- synthKind nullSpanNoFile ty
  -- Generate fresh type variables and apply them to the kind constructor
  (localTyVarContext, baseTy, returnTy') <- fullyApplyType kind (TyVar cVar) ty
  let tyVars = map (\(id, (t, _)) -> (id, t)) localTyVarContext
  st0 <- get
  modify (\st -> st { derivedDefinitions =
                        ((mkId "copyShape", ty), (trivialScheme $ FunTy Nothing Nothing ty returnTy', undefined))
                         : derivedDefinitions st,
                    tyVarContext = tyVarContext st ++ localTyVarContext })

  debugM  "copyShape: " (show returnTy')
  debugM  "copyShape - BaseTy " (show baseTy)
  debugM  "copyShape - local tyVasr " (show localTyVarContext)

 -- st0 <- get
 -- modify (\st -> st {
    --  tyVarContext = tyVarContext st ++ [(kVar, (KCoeffect, ForallQ)), (cVar, (KPromote (TyVar kVar), ForallQ))] ++ localTyVarContext })
  z <- freshIdentifierBase "z" >>= (return . mkId)
  ((shapeTy, returnTy), bodyExpr, primitive) <- deriveCopyShape' s True tyVars baseTy (makeVarUntyped z)
  let tyS = Forall s
              --([(kVar, KCoeffect), (cVar, KPromote (TyVar kVar))] ++ tyVars)
              tyVars
              []
              (FunTy Nothing Nothing baseTy (ProdTy shapeTy returnTy))
  let expr = Val s () True $ Abs () (PVar s () True z) Nothing bodyExpr
  let name = mkId $ "copyShape@" ++ pretty ty
  let def = Def s name True Nothing (EquationList s name True [Equation s name () True [] expr]) tyS
  debugM "copyShape expr" (pretty expr)
  modify (\st -> st { derivedDefinitions = deleteVar' (mkId "copyShape", ty) (derivedDefinitions st)
                    -- Restore type variables and predicate stack
                    , tyVarContext = tyVarContext st0
                    , predicateStack = predicateStack st0 } )
  if primitive
    then return (tyS, Nothing)
    else return (tyS, Just def)

unitType :: Type
unitType = TyCon $ mkId "()"

-- TODO: this returns a pair which says if the derived opertion
-- is actually a primitive; I don't think this is actually needed
-- and at the moment is always false
deriveCopyShape' :: (?globals :: Globals)
  => Span
  -> Bool
  -> Ctxt Kind
  -> Type
  -> Expr () ()
  -> Checker ((Type, Type), (Expr () ()), Bool)
deriveCopyShape' _ _ _ argTy@(leftmostOfApplication -> TyCon (Id "()" "()")) arg = do
  return ((unitType, argTy), makePairUntyped makeUnitIntroUntyped arg, False)

deriveCopyShape' _ _ _ argTy@(TyVar name) arg = do
  return ((unitType, argTy), makePairUntyped makeUnitIntroUntyped arg, False)

deriveCopyShape' s topLevel gamma argTy@(ProdTy t1 t2) arg = do
  x <- freshIdentifierBase "x" >>= (return . mkId)
  y <- freshIdentifierBase "y" >>= (return . mkId)

  ((lShapeTy, lTy), lExpr, _) <- deriveCopyShape' s topLevel gamma t1 (makeVarUntyped x)
  ((rShapeTy, rTy), rExpr, _) <- deriveCopyShape' s topLevel gamma t2 (makeVarUntyped y)

  -- Variables for matching on result of copyShape on left side of pair
  s <- freshIdentifierBase "s" >>= (return . mkId)
  x' <- freshIdentifierBase "x" >>= (return . mkId)

  -- Variables for matching on result of copyShape on right side of pair
  s' <- freshIdentifierBase "s" >>= (return . mkId)
  y' <- freshIdentifierBase "y" >>= (return . mkId)
  let expr =
        makePairElimPUntyped id arg x y (makePairElimPUntyped id lExpr s x' (makePairElimPUntyped id rExpr s' y' (makePairUntyped
                                                                                                                   (makePairUntyped
           (makeVarUntyped s) (makeVarUntyped s'))
         (makePairUntyped
           (makeVarUntyped x') (makeVarUntyped y')))))
  return ((ProdTy lShapeTy rShapeTy, ProdTy lTy rTy), expr, False)

deriveCopyShape' _ _ _ argTy@(leftmostOfApplication -> TyCon (internalName -> id)) arg |
  id == "Int" || id == "Char" || id == "Float" || id == "String "= do
  return ((unitType, argTy), makePairUntyped makeUnitIntroUntyped arg, False)

deriveCopyShape' s topLevel gamma argTy@(leftmostOfApplication -> TyCon name) arg = do
  st <- get
  alreadyDefined <-
    if topLevel
      then return Nothing
      else
        case lookup (mkId "copyShape", TyCon name) (derivedDefinitions st) of
          -- We have it in context, so now we need to apply its type
          Just (tyScheme, _) -> do
            -- freshen the type
            (copyShapeTy, _, _, _constraints, _) <- freshPolymorphicInstance InstanceQ False tyScheme []
            case copyShapeTy of
              t@(FunTy _ mCoeff t1 (ProdTy t2 t3)) -> do
                  -- Its argument must be unified with argTy here
                  (eq, tRes, subst) <- equalTypesRelatedCoeffectsAndUnify s Eq FstIsSpec argTy t1
                  if eq
                    -- Success!
                    then do
                      t3' <- substitute subst t3
                      return (Just ((t2, t3'), App s () True (makeVarUntyped (mkId $ "copyShapea@" <> pretty name)) arg))
                    else do
                      -- Couldn't do the equality.
                      return Nothing
              _ -> return Nothing
          Nothing -> return Nothing
  case alreadyDefined of
    Just (copyShapeResTy, copyShapeExpr) -> return (copyShapeResTy, copyShapeExpr, False)
    Nothing ->
      -- Not already defined...
      -- Get the kind of this type constructor
      case lookup name (typeConstructors st) of
        Nothing -> throw UnboundVariableError { errLoc = s, errId = name }
        Just (kind, _, _) -> do

          -- Get all the data constructors of this type
          mConstructors <- getDataConstructors name
          case mConstructors of
            Nothing -> throw UnboundVariableError { errLoc = s, errId = name }
            Just constructors -> do

              -- For each constructor, build a pattern match and an introduction:
              exprs <- forM constructors (\(dataConsName, (tySch@(Forall _ _ _ dataConsType), coercions)) -> do

                -- Instantiate the data constructor
                (dataConstructorTypeFresh, _, _, _constraint, coercions') <-
                      freshPolymorphicInstance BoundQ True tySch coercions
                -- [Note: this does not register the constraints associated with the data constrcutor]
                dataConstructorTypeFresh <- substitute (flipSubstitution coercions') dataConstructorTypeFresh
                debugM "deriveCopyShape dataConstructorTypeFresh: " (show dataConstructorTypeFresh)
                -- Perform an equality between the result type of the data constructor and the argument type here
                areEq <- equalTypesRelatedCoeffectsAndUnify s Eq PatternCtxt  argTy (resultType dataConstructorTypeFresh)
                case areEq of
                  -- This creates a unification
                  (False, _, _) ->
                      error $ "Cannot derive copyShape for data constructor " <> pretty dataConsName
                  (True, _, unifiers) -> do
                    -- Unify and specialise the data constructor type
                    dataConsType <- substitute (flipSubstitution unifiers) dataConstructorTypeFresh

                    debugM "deriveCopyShape dataConsType: " (show dataConsType)
                    -- Create a variable for each parameter
                    let consParamsTypes = parameterTypes dataConsType
                    debugM "deriveCopyShape cons param types: " (show consParamsTypes)
                    consParamsVars <- forM consParamsTypes (\_ -> freshIdentifierBase "y" >>= (return . mkId))

                    -- Build the pattern for this case
                    let consPattern =
                          PConstr s () True dataConsName (zipWith (\ty var -> PVar s () True var) consParamsTypes consParamsVars)

                    -- Push on all the parameters of a the constructor
                    retTysAndExprs <- zipWithM (\ty var -> do
                            deriveCopyShape' s False gamma ty (makeVarUntyped var))
                              consParamsTypes consParamsVars
                    let (_, exprs, _) = unzip3 retTysAndExprs
--                    let (shapeTys, retTys') = unzip _retTys
                    s' <- freshIdentifierBase "s" >>= (return . mkId)
                    x' <- freshIdentifierBase "x" >>= (return . mkId)
                    let bodyExpr = mkConstructorApplication s dataConsName dataConsType  exprs dataConsType

                    let resExpr = mkConstructorApplication s dataConsName dataConsType  [makeVarUntyped x'] dataConsType
                    let shapeExpr = mkConstructorApplication s dataConsName dataConsType [makeVarUntyped s'] dataConsType
                    let resPair = makePairUntyped shapeExpr resExpr

                    -- Case (Constr x1,..xn) of (s', x') -> Constr s', Constr x'
                    let caseExpr = Case s () True bodyExpr [(PConstr s () True dataConsName [PConstr s () True (mkId ",") [(PVar s () True s'), (PVar s () True x')]], resPair)]

              --      let returnTy = mkTypeApplication dataConsName shapeTys
                    return (consPattern, caseExpr))

              debugM "copyShape retTys:" (show $ exprs)
              let returnShapeTy = mkShapeReturnTy argTy
              -- Got all the branches to make the following case now
              return ((returnShapeTy, argTy), Case s () True arg exprs, False)

      where
        mkShapeReturnTy (TyApp t1 t2) = TyApp (mkShapeReturnTy t1) (TyCon $ mkId "()")
        mkShapeReturnTy (TyCon id) = TyCon id
        mkShapeReturnTy (TyVar id) = TyCon $ mkId "()"
        mkShapeReturnTy ty = ty

deriveCopyShape' s topLevel gamma argTy arg = error ((show argTy) <> "not implemented yet")


deriveDrop :: (?globals :: Globals) => Span -> Type -> Checker (TypeScheme, Maybe (Def () ()))
deriveDrop s ty = do

  -- Create fresh variables for the grades
  kVar <- freshIdentifierBase "k" >>= (return . mkId)
  cVar <- freshIdentifierBase "r" >>= (return . mkId)

  -- Get kind of type constructor
  (kind, _, _) <- synthKind nullSpanNoFile ty
  -- Generate fresh type variables and apply them to the kind constructor
  (localTyVarContext, baseTy, returnTy') <- fullyApplyType kind (TyVar cVar) ty
  let tyVars = map (\(id, (t, _)) -> (id, t)) localTyVarContext
  st0 <- get
  modify (\st -> st { derivedDefinitions =
                        ((mkId "drop", ty), (trivialScheme $ FunTy Nothing Nothing ty returnTy', undefined))
                         : derivedDefinitions st,
                    tyVarContext = tyVarContext st ++ localTyVarContext })

  z <- freshIdentifierBase "z" >>= (return . mkId)
  (returnTy, bodyExpr, primitive) <- deriveDrop' s True tyVars baseTy (makeVarUntyped z)
  let tyS = Forall s
              tyVars
              []
              (FunTy Nothing Nothing baseTy returnTy)
  let expr = Val s () True $ Abs () (PVar s () True z) Nothing bodyExpr
  let name = mkId $ "drop@" ++ pretty ty
  let def = Def s name True Nothing (EquationList s name True [Equation s name () True [] expr]) tyS
  modify (\st -> st { derivedDefinitions = deleteVar' (mkId "drop", ty) (derivedDefinitions st)
                    -- Restore type variables and predicate stack
                    , tyVarContext = tyVarContext st0
                    , predicateStack = predicateStack st0 } )
  if primitive
    then return (tyS, Nothing)
    else return (tyS, Just def)


deriveDrop' :: (?globals :: Globals)
  => Span
  -> Bool
  -> Ctxt Kind
  -> Type
  -> Expr () ()
  -> Checker (Type, Expr () (), Bool)
deriveDrop' _ _ _ argTy@(leftmostOfApplication -> TyCon (Id "()" "()")) arg = do
  return (TyCon $ mkId "()", makeUnitIntroUntyped, False)

deriveDrop' _ _ _ argTy@(leftmostOfApplication -> TyCon (Id "Int" "Int")) arg = do
  return (TyCon $ mkId "()", (App nullSpanNoFile () False (makeVarUntyped (mkId "drop@Int")) arg), True)

deriveDrop' _ _ _ argTy@(leftmostOfApplication -> TyCon (Id "Char" "Char")) arg = do
  return (TyCon $ mkId "()", (App nullSpanNoFile () False (makeVarUntyped (mkId "drop@Char")) arg), True)

deriveDrop' _ _ _ argTy@(leftmostOfApplication -> TyCon (Id "Float" "Float")) arg = do
  return (TyCon $ mkId "()", (App nullSpanNoFile () False (makeVarUntyped (mkId "drop@Float")) arg), True)

deriveDrop' _ _ _ argTy@(leftmostOfApplication -> TyCon (Id "String" "String")) arg = do
  return (TyCon $ mkId "()", (App nullSpanNoFile () False (makeVarUntyped (mkId "drop@String")) arg), True)

deriveDrop' _ _ _ argTy@(TyVar name) arg = do
  return (TyCon $ mkId "()", makeUnitIntroUntyped, False)

deriveDrop' s topLevel gamma argTy@(ProdTy t1 t2) arg = do
  x <- freshIdentifierBase "x" >>= (return . mkId)
  y <- freshIdentifierBase "y" >>= (return . mkId)

  (lTy, lExpr, _) <- deriveDrop' s topLevel gamma t1 (makeVarUntyped x)
  (rTy, rExpr, _) <- deriveDrop' s topLevel gamma t2 (makeVarUntyped y)

  let expr = makePairElimPUntyped id arg x y (makeUnitElimPUntyped id lExpr (makeUnitElimPUntyped id rExpr makeUnitIntroUntyped))
  debugM "expr: " (pretty expr)

  return (TyCon $ mkId "()", expr, False)


deriveDrop' s topLevel gamma argTy@(leftmostOfApplication -> TyCon name) arg = do
  st <- get
  alreadyDefined <-
    if topLevel
      then return Nothing
      else
        case lookup (mkId "drop", TyCon name) (derivedDefinitions st) of
          -- We have it in context, so now we need to apply its type
          Just (tyScheme, _) -> do
            -- freshen the type
            (dropTy, _, _, _constraints, _) <- freshPolymorphicInstance InstanceQ False tyScheme []
            case dropTy of
              t@(FunTy _ mCoeff t1 t2) -> do
                  -- Its argument must be unified with argTy here
                  (eq, tRes, subst) <- equalTypesRelatedCoeffectsAndUnify s Eq FstIsSpec argTy t1
                  if eq
                    -- Success!
                    then do
                      return (Just (TyCon $ mkId "()", App s () True (makeVarUntyped (mkId $ "drop@" <> pretty name)) arg))
                    else do
                      -- Couldn't do the equality.
                      return Nothing
              _ -> return Nothing
          Nothing -> return Nothing
  case alreadyDefined of
    Just (dropTy, dropExpr) -> return (dropTy, dropExpr, False)
    Nothing ->
      -- Not already defined...
      -- Get the kind of this type constructor
      case lookup name (typeConstructors st) of
        Nothing -> throw UnboundVariableError { errLoc = s, errId = name }
        Just (kind, _, _) -> do

          -- Get all the data constructors of this type
          mConstructors <- getDataConstructors name
          case mConstructors of
            Nothing -> throw UnboundVariableError { errLoc = s, errId = name }
            Just constructors -> do

              -- For each constructor, build a pattern match and an introduction:
              exprs <- forM constructors (\(dataConsName, (tySch@(Forall _ _ _ dataConsType), coercions)) -> do

                -- Instantiate the data constructor
                (dataConstructorTypeFresh, _, _, _constraint, coercions') <-
                      freshPolymorphicInstance BoundQ True tySch coercions
                -- [Note: this does not register the constraints associated with the data constrcutor]
                dataConstructorTypeFresh <- substitute (flipSubstitution coercions') dataConstructorTypeFresh
                debugM "deriveDrop dataConstructorTypeFresh: " (show dataConstructorTypeFresh)
                -- Perform an equality between the result type of the data constructor and the argument type here
                areEq <- equalTypesRelatedCoeffectsAndUnify s Eq PatternCtxt  argTy (resultType dataConstructorTypeFresh)
                case areEq of
                  -- This creates a unification
                  (False, _, _) ->
                      error $ "Cannot derive drop for data constructor " <> pretty dataConsName
                  (True, _, unifiers) -> do
                    -- Unify and specialise the data constructor type
                    dataConsType <- substitute unifiers dataConstructorTypeFresh

                    debugM "deriveDrop dataConsType: " (show dataConsType)
                    -- Create a variable for each parameter
                    let consParamsTypes = parameterTypes dataConsType
                    consParamsVars <- forM consParamsTypes (\_ -> freshIdentifierBase "y" >>= (return . mkId))

                    -- Build the pattern for this case
                    let consPattern =
                          PConstr s () True dataConsName (zipWith (\ty var -> PVar s () True var) consParamsTypes consParamsVars)

                    -- Drop on all the parameters of the constructor
                    retTysAndExprs <- zipWithM (\ty var -> do
                            let (defs, def') = (map fst (derivedDefinitions st), map (fst . snd) (derivedDefinitions st))
                            let defs'' = zip defs def'
                            debugM "recursing " (show gamma <> " " <> show ty <> " " <> show var <> " " <> show defs'')
                            deriveDrop' s False gamma ty (makeVarUntyped var))
                              consParamsTypes consParamsVars
                    x <- freshIdentifierBase "x" >>= (return . mkId)
                    return (consPattern, makeUnitIntroUntyped))

              -- Got all the branches to make the following case now
              return (TyCon $ mkId "()", Case s () True arg exprs, False)

deriveDrop' s topLevel gamma argTy arg = error (show argTy <> "not implemented yet")
