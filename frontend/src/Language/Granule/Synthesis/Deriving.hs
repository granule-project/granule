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
import Language.Granule.Checker.Predicates (Quantifier(..), Constraint(..))
import Language.Granule.Checker.Variables
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Types

import Language.Granule.Synthesis.Builders

import Language.Granule.Utils
import Control.Monad (zipWithM, forM)

  {-
  Module for automatically deriving graded linear logical
  operations based on types.
  -}

pbox :: Coeffect -> Type -> Pattern Type -> Pattern Type
pbox c t = PBox nullSpanNoFile (Box c t) True

derivePush :: (?globals :: Globals) => Span -> Type -> Checker (TypeScheme, Def () Type)
derivePush s ty = do
  -- Create fresh variables for the grades
  kVar <- freshIdentifierBase "k" >>= (return . mkId)
  cVar <- freshIdentifierBase "r" >>= (return . mkId)

  -- Get kind of type constructor
  kind <- inferKindOfType nullSpanNoFile ty
  -- Generate fresh type variables and apply them to the kind constructor
  (tyVarsContext, baseTy, _) <- fullyApplyType kind (CVar cVar) ty
  let tyVars = map (\(id, (t, _)) -> (id, t)) tyVarsContext
  let argTy = Box (CVar cVar) baseTy

  -- Give a name to the input
  z <- freshIdentifierBase "z" >>= (return . mkId)
  (returnTy, bodyExpr) <-
    derivePush' s (CVar cVar) [] tyVars baseTy (makeVar z (trivialScheme argTy))

  -- Build derived type scheme
  let tyS = Forall s
              ([(kVar, KCoeffect), (cVar, KPromote (TyVar kVar))] ++ tyVars)
              []
              (FunTy Nothing argTy returnTy)
  -- Build the expression
  let expr = Val s (FunTy Nothing argTy returnTy) True
              $ Abs returnTy (PVar s argTy True z) Nothing bodyExpr
  let name = mkId $ "push" ++ pretty ty
  return $
    (tyS, Def s name True
            (EquationList s name True
               [Equation s name (unforall tyS) True [] expr]) tyS)

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
            -> Coeffect -> Ctxt Id -> Ctxt Kind -> Type -> Expr () Type -> Checker (Type, Expr () Type)

-- Type variable case: push_alpha arg = arg

derivePush' s c _sigma gamma argTy@(TyVar n) arg = do
  case lookup n gamma of
    Just _ -> return (Box c argTy, arg)
    Nothing -> do
      -- For arguments which are type variables but not parameters
      -- to this type constructor, then we need to do an unboxing
      x <- freshIdentifierBase "x" >>= (return . mkId)
      let expr = makeUnboxP x arg (trivialScheme argTy) (Box c argTy) argTy (makeVar' x argTy)
      return (argTy, expr)

-- Unit case:  push_() arg = (case arg of () -> ()) : ())
derivePush' s c _sigma gamma argTy@(TyCon (internalName -> "()")) arg = do
  let ty  = argTy
  return (ty, makeUnitElimP (pbox c argTy) arg makeUnitIntro (trivialScheme argTy))

-- Pair case: push_(t1,t2) arg = (case arg of (x, y) -> (push_t1 [x], push_t2 [y])
derivePush' s c _sigma gamma argTy@(ProdTy t1 t2) arg = do
  x <- freshIdentifierBase "x" >>= (return . mkId)
  y <- freshIdentifierBase "y" >>= (return . mkId)
  -- Induction
  (leftTy, leftExpr)   <- derivePush' s c _sigma gamma t1 (makeBox (trivialScheme $ Box c t1) (makeVar' x t1))
  (rightTy, rightExpr) <- derivePush' s c _sigma gamma t2 (makeBox (trivialScheme $ Box c t2) (makeVar' y t2))
  -- Build eliminator
  let returnTy = ProdTy leftTy rightTy
  return (returnTy, makePairElimP (pbox c argTy) arg x y (trivialScheme returnTy) t1 t2
               (makePair leftTy rightTy leftExpr rightExpr))

derivePush' s c _sigma gamma argTy@(leftmostOfApplication -> TyCon name) arg = do
  mConstructors <- getDataConstructors name
  case mConstructors of
    Nothing -> throw UnboundVariableError { errLoc = s, errId = name }
    Just constructors -> do

      -- For each constructor, build a pattern match and an introduction:
      tysAndCases <- forM constructors (\(dataConsName, (tySch, coercions)) -> do
        -- First, we do something that is a bit like pattern typing

        -- Instantiate the data constructor
        (dataConstructorTypeFresh, freshTyVarsCtxt, freshTyVarSubst, _constraint, coercions') <-
          freshPolymorphicInstance BoundQ True tySch coercions
        -- [Note: this does not register the constraints associated with the data constrcutor]
        dataConstructorTypeFresh <- substitute (flipSubstitution coercions') dataConstructorTypeFresh
        -- Perform an equality between the result type of the data constructor and the argument type here
        areEq <- equalTypesRelatedCoeffectsAndUnify s Eq PatternCtxt (resultType dataConstructorTypeFresh) argTy
        case areEq of
          -- This creates a unification
          (True, _, unifiers) -> do
            -- Unify and specialise the data constructor type
            dataConstructorIndexRewritten <- substitute unifiers dataConstructorTypeFresh
            dataConsType <- substitute coercions' dataConstructorIndexRewritten

            -- Types of every argument and the variable used for it
            let consParamsTypes = parameterTypes dataConsType
            consParamsVars <- forM consParamsTypes (\_ -> freshIdentifierBase "y" >>= (return . mkId))

            -- Build the pattern for this case
            let consPattern =
                  PConstr s (resultType dataConsType) True name (zipWith (\ty var -> PVar s ty True var) consParamsTypes consParamsVars)
            let consPatternBoxed =
                  PBox s (Box c (resultType dataConsType)) True consPattern

             -- Push on all the parameters of a the constructor
            retTysAndExprs <- zipWithM (\ty var ->
                 derivePush' s c _sigma gamma ty (makeBox (trivialScheme $ Box c ty) (makeVar' var ty)))
                    consParamsTypes consParamsVars
            let (retTys, exprs) = unzip retTysAndExprs

            -- Now constructor an application of a constructor
            (tyA, _, _, constraintsA, coercionsA') <- freshPolymorphicInstance InstanceQ False tySch coercions
            -- Apply coercions
            tyA <- substitute coercionsA' tyA

            argsEq <- zipWithM (\appliedTy consArgTy ->
                        equalTypesRelatedCoeffectsAndUnify s Eq SndIsSpec appliedTy consArgTy) retTys (parameterTypes tyA)
            let (eqs, _types, substs) = unzip3 argsEq
            if and eqs
              then do
                finalSubst <- combineManySubstitutions s substs
                consType <- substitute finalSubst tyA
                let returnTy = resultType consType
                let bodyExpr = mkConstructorApplication s name consType exprs consType
                return (returnTy, (consPatternBoxed, bodyExpr))

            else error $ "Cannot derive for " <> pretty name <> " due to a typing error"

          (False, _, _) ->
            error $ "Cannot derive push for data constructor " <> pretty dataConsName)

      -- Got all the barnches to make the following case now
      let returnTy = head (map fst tysAndCases)
      let cases    = map snd tysAndCases
      return (returnTy, Case s returnTy True arg cases)


derivePush' s _ _ _ ty _ = do
  error $ "Cannot push derive for type " ++ pretty ty

-- Based on its type, apply a list of arguments to a ty constructor
mkConstructorApplication :: (?globals :: Globals) => Span -> Id -> Type -> [Expr () Type] -> Type -> Expr () Type
mkConstructorApplication s name consType [] t =
  Val s consType True (Constr consType name [])

mkConstructorApplication s name consType (expr:exprs) (FunTy _ t1 t2) =
  App s t2 True (mkConstructorApplication s name consType exprs t2) expr

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
