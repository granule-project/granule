module Language.Granule.Synthesis.Deriving
  (derivePush, derivePull) where

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Span
import Language.Granule.Context

import Language.Granule.Checker.Predicates (Constraint(..))
import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates (Quantifier(..))
import Language.Granule.Checker.Types (SpecIndicator(..), equalTypesRelatedCoeffectsAndUnify)
import Language.Granule.Checker.Variables
import Language.Granule.Checker.Substitution(substitute, freshPolymorphicInstance)
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
  kind <- inferKindOfType nullSpanNoFile ty
  -- Generate fresh type variables and apply them to the kind constructor
  (localTyVarContext, baseTy, returnTy') <- fullyApplyType kind (CVar cVar) ty
  let tyVars = map (\(id, (t, _)) -> (id, t)) localTyVarContext
  let argTy = Box (CVar cVar) baseTy

  -- For the purposes of recursive types, temporarily 'register' a dummy
  -- definition for this push
  st0 <- get
  modify (\st -> st { derivedDefinitions =
                        ((mkId "push", ty), (trivialScheme $ FunTy Nothing argTy returnTy', undefined))
                         : derivedDefinitions st
                    , tyVarContext = tyVarContext st ++ [(kVar, (KCoeffect, ForallQ)), (cVar, (KPromote (TyVar kVar), ForallQ))] ++ localTyVarContext })

  -- Give a name to the input
  z <- freshIdentifierBase "z" >>= (return . mkId)
  (returnTy, bodyExpr, isPoly) <-
    derivePush' s True (CVar cVar) [] tyVars baseTy (makeVarUntyped z)

  -- Build derived type scheme
  let constraints =
        if isPoly
          then [TyInfix TyOpLesserEq (TyInt 1) (TyVar cVar)]
          else []
  let tyS = Forall s
              ([(kVar, KCoeffect), (cVar, KPromote (TyVar kVar))] ++ tyVars)
              constraints
              (FunTy Nothing argTy returnTy)
  -- Build the expression
  let expr = Val s () True $ Abs () (PVar s () True z) Nothing bodyExpr
  let name = mkId $ "push@" ++ pretty ty

  -- Remove the dummy definition here
  modify (\st -> st { derivedDefinitions = deleteVar' (mkId "push", ty) (derivedDefinitions st)
                    -- Restore type variables and predicate stack
                    , tyVarContext = tyVarContext st0
                    , predicateStack = predicateStack st0 } )
  return $
    (tyS, Def s name True
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
            -> Coeffect -> Ctxt Id -> Ctxt Kind -> Type -> Expr () () -> Checker (Type, Expr () (), Bool)

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
  debugM "derive-push" ("TyCon case " <> pretty argTy)
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
              t@(FunTy _ t1 t2) -> do
                  -- Its argument must be unified with argTy here
                  (eq, tRes, subst) <- equalTypesRelatedCoeffectsAndUnify s Eq FstIsSpec (Box c argTy) t1
                  if eq
                    -- Success!
                    then do
                      t2' <- substitute subst t2
                      return (Just (t2', App s () True (makeVarUntyped (mkId $ "push@" <> pretty name)) arg))
                    else do
                      -- Couldn't do the equality.
                      debugM "derive-push" ("no eq for " ++ pretty argTy ++ " and " ++ pretty t1)
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

                debugM "deriv-push - dataConstructorTypeFresh" (pretty dataConstructorTypeFresh)

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

mkConstructorApplication s name consType (expr:exprs) (FunTy _ t1 t2) =
  App s () True (mkConstructorApplication s name consType exprs t2) expr

mkConstructorApplication s name consType  _ _ =
  error $ "In making constructor for " ++ pretty name


derivePull :: (?globals :: Globals) => Span -> Type -> Checker (TypeScheme, Def () ())
derivePull s ty = do
  -- Create fresh variables for the grades
  kVar <- freshIdentifierBase "k" >>= (return . mkId)
  cVar <- freshIdentifierBase "r" >>= (return . mkId)

  -- Get kind of type constructor
  kind <- inferKindOfType nullSpanNoFile ty
  -- Generate fresh type variables and apply them to the kind constructor
  (localTyVarContext, baseTy, returnTy') <- fullyApplyType kind (CVar cVar) ty
  let tyVars = map (\(id, (t, _)) -> (id, t)) localTyVarContext

  z <- freshIdentifierBase "z" >>= (return . mkId)
  (returnTy, bodyExpr, coeff) <-
    derivePull' s [] tyVars returnTy' (makeVarUntyped z)

  case coeff of
    Just c -> do
      let tyS = Forall s
              ([(kVar, KCoeffect), (cVar, KPromote (TyVar kVar))] ++ tyVars)
              []
              (FunTy Nothing returnTy' (Box c returnTy))
      let expr = Val s () True $ Abs () (PVar s () True z) Nothing bodyExpr
      let name = mkId $ "pull@" ++ pretty ty

      return $
        (tyS, Def s name True
            (EquationList s name True
               [Equation s name () True [] expr]) tyS)
    Nothing -> error "shouldn't be reachable"


derivePull'  :: (?globals :: Globals) =>  Span -> Ctxt Id -> Ctxt Kind -> Type -> Expr () () -> Checker (Type, Expr () (), Maybe Coeffect)

derivePull' s _sigma gamma argTy@(Box c t) arg = do
  (returnTy, expr, coeff) <- derivePull' s _sigma gamma t arg
  case coeff of
    Just c' -> return (returnTy, expr, Just $ CMeet c c')
    _ -> return (returnTy, expr, Just $ CMeet c c)

derivePull' s _sigma gamma argTy@(TyVar n) arg = do
  case lookup n gamma of
    Just _ -> return (TyVar n, arg, Nothing)
    Nothing -> error "do this in a bit"
     -- do
     -- -- For arguments which are type variables but not parameters
     -- -- to this type constructor, then we need to do an unboxing
     -- x <- freshIdentifierBase "x" >>= (return . mkId)
     -- let expr = makeUnboxUntyped x arg (makeVarUntyped x)
     -- return (argTy, expr)

derivePull' s _sigma gamma argTy@(ProdTy t1 t2) arg = do
  x <- freshIdentifierBase "x" >>= (return . mkId)
  y <- freshIdentifierBase "y" >>= (return . mkId)
  -- Induction
  (leftTy, leftExpr, lCoeff)   <- derivePull' s _sigma gamma t1 (makeVarUntyped x)
  (rightTy, rightExpr, rCoeff) <- derivePull' s _sigma gamma t2 (makeVarUntyped y)
--  let coeffs = (singleton c1) `union` (singleton c2) `union` rCoeffs `union` lCoeffs
  let returnTy = (ProdTy leftTy rightTy)
  case (lCoeff, rCoeff) of
    (Just c, Just c') -> return (returnTy, makePairElimPUntyped' pbox arg x y
                     (makeBoxUntyped (makePairUntyped leftExpr rightExpr)), Just $ CMeet c c')
    (_, _) -> return (returnTy, makePairElimPUntyped' pbox arg x y
                     (makeBoxUntyped (makePairUntyped leftExpr rightExpr)), Nothing)

  -- Build eliminator

derivePull' _ _ _ ty _ = error $ "still to come!" <> show ty

-- Given a kind for a type constructor, fully apply the type constructor
-- generator with fresh type variables for each parameter and return a type-variable
-- context containing these variables as well as the applied type along with
-- a pair of the applied type (e.g., F a b) [called the base type]
-- and the type for argument of a pull (e.g., F ([] r a) ([] r b))
fullyApplyType :: (?globals :: Globals)
                   => Kind -> Coeffect -> Type -> Checker (Ctxt (Kind, Quantifier), Type, Type)
fullyApplyType k r t = fullyApplyType' k r t t

fullyApplyType' :: (?globals :: Globals)
                    => Kind -> Coeffect -> Type -> Type -> Checker (Ctxt (Kind, Quantifier), Type, Type)
fullyApplyType' KType r baseTy argTy =
  return ([], baseTy, argTy)

fullyApplyType' (KFun t1 t2) r baseTy argTy = do
  -- Fresh ty variable
  tyVar <- freshIdentifierBase "a" >>= (return . mkId)
  -- Apply to the base type
  let baseTy' = TyApp baseTy (TyVar tyVar)
  -- Apply to the "argument of push" type
  let argTy'  =
       case t1 of
         KType -> TyApp argTy (Box r (TyVar tyVar))
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
                   => Type -> Kind -> Coeffect -> Maybe Type
objectMappingWithBox t k r = objectMappingWithBox' t (reverse $ parameterKinds k) r

objectMappingWithBox' :: (?globals :: Globals)
                    => Type -> [Kind] -> Coeffect -> Maybe Type

objectMappingWithBox' t [] _ = return t

objectMappingWithBox' (TyApp t1 t2) (k:ks) r = do
  t <- objectMappingWithBox' t1 ks r
  case k of
    -- Only added boxes on types
    KType -> return $ TyApp t (Box r t2)
    _     -> return $ TyApp t t2

objectMappingWithBox' _ _ _ = Nothing

deleteVar' :: Eq a => a -> [(a, t)] -> [(a, t)]
deleteVar' _ [] = []
deleteVar' x ((y, b) : m) | x == y = deleteVar' x m
                          | otherwise = (y, b) : deleteVar' x m