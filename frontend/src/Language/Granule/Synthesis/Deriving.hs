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

import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates (Quantifier(..))
import Language.Granule.Checker.Variables
import Language.Granule.Checker.SubstitutionContexts

import Language.Granule.Synthesis.Builders

import Language.Granule.Utils
import Control.Monad.State.Strict (get)
import Control.Monad (zipWithM, forM)

  {-
  Module for automatically deriving graded linear logical
  operations based on types.
  -}

pbox :: Pattern () -> Pattern ()
pbox = PBox nullSpanNoFile () True

derivePush :: (?globals :: Globals) => Span -> Type -> Checker (TypeScheme, Def () ())
derivePush s ty = do
  -- Create fresh variables for the grades
  kVar <- freshIdentifierBase "k" >>= (return . mkId)
  cVar <- freshIdentifierBase "r" >>= (return . mkId)

  -- Get kind of type constructor
  kind <- inferKindOfType nullSpanNoFile ty
  -- Generate fresh type variables and apply them to the kind constructor
  (localTyVarContext, baseTy, _) <- fullyApplyType kind (CVar cVar) ty
  let tyVars = map (\(id, (t, _)) -> (id, t)) localTyVarContext
  let argTy = Box (CVar cVar) baseTy

  -- Give a name to the input
  z <- freshIdentifierBase "z" >>= (return . mkId)
  (returnTy, bodyExpr) <-
    derivePush' s (CVar cVar) [] tyVars baseTy (makeVarUntyped z)

  -- Build derived type scheme
  let tyS = Forall s
              ([(kVar, KCoeffect), (cVar, KPromote (TyVar kVar))] ++ tyVars)
              []
              (FunTy Nothing argTy returnTy)
  -- Build the expression
  let expr = Val s () True $ Abs () (PVar s () True z) Nothing bodyExpr
  let name = mkId $ "push" ++ pretty ty

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
derivePush' :: (?globals :: Globals)
            => Span
            -> Coeffect -> Ctxt Id -> Ctxt Kind -> Type -> Expr () () -> Checker (Type, Expr () ())

-- Type variable case: push_alpha arg = arg

derivePush' s c _sigma gamma argTy@(TyVar n) arg = do
  case lookup n gamma of
    Just _ -> return (Box c argTy, arg)
    Nothing -> do
      -- For arguments which are type variables but not parameters
      -- to this type constructor, then we need to do an unboxing
      x <- freshIdentifierBase "x" >>= (return . mkId)
      let expr = makeUnboxUntyped x arg (makeVarUntyped x)
      return (argTy, expr)

-- Unit case:  push_() arg = (case arg of () -> ()) : ())
derivePush' s c _sigma gamma argTy@(TyCon (internalName -> "()")) arg = do
  let ty  = argTy
  return (ty, makeUnitElimPUntyped pbox arg makeUnitIntroUntyped)

-- Pair case: push_(t1,t2) arg = (case arg of (x, y) -> (push_t1 [x], push_t2 [y])
derivePush' s c _sigma gamma argTy@(ProdTy t1 t2) arg = do
  x <- freshIdentifierBase "x" >>= (return . mkId)
  y <- freshIdentifierBase "y" >>= (return . mkId)
  -- Induction
  (leftTy, leftExpr)   <- derivePush' s c _sigma gamma t1 (makeBoxUntyped (makeVarUntyped x))
  (rightTy, rightExpr) <- derivePush' s c _sigma gamma t2 (makeBoxUntyped (makeVarUntyped y))
  -- Build eliminator
  let returnTy = ProdTy leftTy rightTy
  return (returnTy, makePairElimPUntyped pbox arg x y
                     (makePairUntyped leftExpr rightExpr))

derivePush' s c _sigma gamma argTy@(leftmostOfApplication -> TyCon name) arg = do
  st <- get
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

              -- Create a variable for each parameter
              let consParamsTypes = parameterTypes dataConsType
              consParamsVars <- forM consParamsTypes (\_ -> freshIdentifierBase "y" >>= (return . mkId))

              -- Build the pattern for this case
              let consPattern =
                    PConstr s () True dataConsName (zipWith (\ty var -> PVar s () True var) consParamsTypes consParamsVars)
              let consPatternBoxed =
                    PBox s () True consPattern

              -- Push on all the parameters of a the constructor
              retTysAndExprs <- zipWithM (\ty var ->
                      derivePush' s c _sigma gamma ty (makeBoxUntyped (makeVarUntyped var)))
                        consParamsTypes consParamsVars
              let (_retTys, exprs) = unzip retTysAndExprs

              let bodyExpr = mkConstructorApplication s dataConsName dataConsType exprs dataConsType
              return (consPatternBoxed, bodyExpr))

          -- Got all the branches to make the following case now
          case objectMappingWithBox argTy kind c of
            Just returnTy -> return (returnTy, Case s () True arg cases)
            Nothing -> error $ "Cannot push derive for type " ++ pretty argTy ++ " due to typing"

derivePush' s _ _ _ ty _ = do
  error $ "Cannot push derive for type " ++ pretty ty

-- Based on its type, apply a list of arguments to a ty constructor
mkConstructorApplication :: (?globals :: Globals) => Span -> Id -> Type -> [Expr () ()] -> Type -> Expr () ()
mkConstructorApplication s name consType [] t =
  Val s () True (Constr () name [])

mkConstructorApplication s name consType (expr:exprs) (FunTy _ t1 t2) =
  App s () True (mkConstructorApplication s name consType exprs t2) expr

mkConstructorApplication s name consType  _ _ =
  error $ "In making constructor for " ++ pretty name

derivePull :: Ctxt (Ctxt (TypeScheme, Substitution)) -> Type -> (TypeScheme, Def () ())
derivePull = error "stub"

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
