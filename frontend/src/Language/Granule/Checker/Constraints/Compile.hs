{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}

-- | Provides helpers for compiling constraints
module Language.Granule.Checker.Constraints.Compile
   (compileTypeConstraintToConstraint
  , enforceConstraints
  , dischargedTypeConstraints) where

import Control.Monad.State.Strict
import Control.Monad.Identity

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Kinding (checkKind, synthKind)

import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers

import Language.Granule.Checker.Primitives (nonDropable)

import Language.Granule.Utils

compileTypeConstraintToConstraint ::
    (?globals :: Globals) => Span -> Type -> Checker (Either Pred Type)
compileTypeConstraintToConstraint s (TyInfix op t1 t2) = do
  (k, _, _) <- synthKind s t1
  (result, putChecker) <- peekChecker (checkKind s t2 k)
  case result of
    Right _ -> do
      putChecker
      pred <- compileAtType s op t1 t2 k
      return $ Left pred
    Left _ ->
      case k of
        TyVar v -> do
          st <- get
          case lookup v (tyVarContext st) of
            Just (_, ForallQ) | isGenericCoeffectExpression t2 -> do
              pred <- compileAtType s op t1 t2 (TyVar v)
              return $ Left pred

            _ -> throw $ UnificationError s t1 t2
        _ -> throw $ UnificationError s t1 t2

-- Some other kind of constraint that has to be registered for this equation
compileTypeConstraintToConstraint s t =
  return $ Right t

compileAtType :: (?globals :: Globals) => Span -> TypeOperator -> Type -> Type -> Type -> Checker Pred
compileAtType s op c1 c2 coeffTy = do
  case op of
    TyOpEq -> return $ Con (Eq s c1 c2 coeffTy)
    TyOpNotEq -> return $ Con (Neq s c1 c2 coeffTy)
    TyOpLesserNat -> return $ Con (Lt s c1 c2)
    TyOpGreaterNat -> return $ Con (Gt s c1 c2)
    TyOpLesserEq -> return $ Con (ApproximatedBy s c1 c2 coeffTy)
    TyOpGreaterEq -> return $ Con (ApproximatedBy s c2 c1 coeffTy)
    TyOpLesserEqNat -> return $ Con (LtEq s c1 c2)
    TyOpGreaterEqNat -> return $ Con (GtEq s c1 c2)
    TyOpHsup         -> return $ Con (Hsup s c1 c2 coeffTy)
    TyOpMutable      -> return $ Disj [(Con (Eq s c1 (TyCon (mkId $ "Star")) coeffTy)), (Con (Eq s c1 (TyFraction 1) coeffTy))]
    TyOpImpl         -> do
      p1 <- compileTypeConstraintToConstraint s c1
      p2 <- compileTypeConstraintToConstraint s c2
      case (p1, p2) of
        (Left p1, Left p2) -> return $ Impl [] p1 p2
        -- Something odd
        _                  -> return $ Conj []
    _ -> error $ pretty s <> ": I don't know how to compile binary operator " <> pretty op


-- Given a list of type constraints (things to the left of a =>)
-- registers those which are graded things as predicates
-- and returns those which are 'regular' type constraints
enforceConstraints :: (?globals :: Globals) => Span -> [Type] -> Checker [Type]
enforceConstraints s [] = return []
enforceConstraints s (t:ts) = do
  sx <- compileTypeConstraintToConstraint s t
  case sx of
    Left pred -> do
      addPredicate pred
      enforceConstraints s ts

    Right t -> do
      ts' <- enforceConstraints s ts
      return $ t : ts'

-- Match provided constraints (assumptions) against wanted constraints /
-- see if the wanted constraints are already satisfied
dischargedTypeConstraints :: (?globals :: Globals) => Span -> [Type] -> [Type] -> Checker ()
dischargedTypeConstraints s provided [] = return ()
dischargedTypeConstraints s provided (w : ws) =
  if w `elem` provided
    then dischargedTypeConstraints s provided ws
    else do
      b <- isDefinedConstraint s w
      if b
        then dischargedTypeConstraints s provided ws
        else throw $ TypeConstraintNotSatisfied s w

-- TODO: provide some way to define this related with user syntax
isDefinedConstraint :: (?globals :: Globals) => Span -> Type -> Checker Bool
isDefinedConstraint _ (TyApp (TyCon (internalName -> "SingleAction")) protocol)
  = return (singleAction protocol)

isDefinedConstraint _ (TyApp (TyCon (internalName -> "ReceivePrefix")) protocol)
  = return (receivePrefix protocol)

isDefinedConstraint s (TyApp (TyCon (internalName -> "Sends")) protocol)
  = sends s protocol

isDefinedConstraint s (TyApp (TyCon (internalName -> "ExactSemiring")) semiring)
  = return (exactSemiring semiring)

isDefinedConstraint s (TyApp (TyCon (internalName -> "Dropable")) typ)
  = return (dropable typ)

isDefinedConstraint s (TyApp (TyCon (internalName -> "Cloneable")) typ)
  = return (cloneable typ)

isDefinedConstraint _ _
  = return False

receivePrefix :: Type -> Bool
receivePrefix (TyApp (TyApp (TyCon (internalName -> "Recv")) t) p) = True
receivePrefix (TyApp
           (TyApp (TyCon (internalName -> "Offer")) _) _) = True
receivePrefix _ = False

-- TODO: this could probably be made into a pure function now
sends :: (?globals :: Globals) => Span -> Type -> Checker Bool
sends _ (TyCon (internalName -> "End")) = return True
sends s (TyApp (TyApp (TyCon (internalName -> "Send")) t) p) = sends s p
sends s (TyApp (TyApp (TyCon (internalName -> "Recv")) t) p) = return False
sends s (TyApp (TyApp (TyCon (internalName -> "Offer")) t) t') = return False
sends s (TyApp (TyApp (TyCon (internalName -> "Select")) t) t') = do
  b  <- sends s t
  b' <- sends s t'
  return $ b && b'
sends _ _ = return False

singleAction :: Type -> Bool
singleAction (TyCon (internalName -> "End")) = True
singleAction (TyApp
              (TyApp (TyCon (internalName -> "Send")) t)
              (TyCon (internalName -> "End"))) = True
singleAction (TyApp
              (TyApp (TyCon (internalName -> "Recv")) t)
              (TyCon (internalName -> "End"))) = True
singleAction (TyApp
              (TyApp (TyCon (internalName -> "Offer"))
              (TyCon (internalName -> "End")))
              (TyCon (internalName -> "End"))) = True
singleAction (TyApp
              (TyApp (TyCon (internalName -> "Select"))
              (TyCon (internalName -> "End")))
              (TyCon (internalName -> "End"))) = True
singleAction _ = False

exactSemiring :: Type -> Bool
exactSemiring (TyCon (internalName -> "Nat")) = True
exactSemiring (TyApp
               (TyCon (internalName -> "Ext")) s) = exactSemiring s
exactSemiring (TyApp
                (TyApp (TyCon (internalName -> ",,"))
                 s1)
                 s2) = exactSemiring s1 && exactSemiring s2
exactSemiring _ = False

cloneable :: Type -> Bool
cloneable (TyApp
  (TyCon (internalName -> "FloatArray")) _ ) = True
cloneable (TyApp
  (TyApp
    (TyCon (internalName -> "Ref")) _) t) = cloneable t
cloneable (TyApp
  (TyApp
    (TyCon (internalName -> ",")) x) y) = cloneable x && cloneable y
cloneable _ = False

dropable :: Type -> Bool
dropable =
    runIdentity . typeFoldM (TypeFold
      { tfTy = \_ -> return $ True
      , tfFunTy = \_ c x y -> return y
      , tfTyCon = \id -> return $ not (id `elem` nonDropable)
      , tfBox = \x y -> return (x && y)
      , tfDiamond = \x y -> return $ (x && y)
      , tfStar = \x y -> return $ (x && y)
      , tfBorrow = \x y -> return $ (x && y)
      , tfTyVar = \_ -> return False
      , tfTyApp = \x y -> return x
      , tfTyInt = \_ -> return True
      , tfTyRational = \_ -> return True
      , tfTyFraction = \_ -> return True
      , tfTyGrade = \_ _ -> return True
      , tfTyInfix = \_ x y -> return (x && y)
      , tfSet = \_ _ -> return  True
      , tfTyCase = \_ _ -> return False
      , tfTySig = \t _ _ -> return t
      , tfTyExists = \_ _ x -> return x
      , tfTyForall = \_ _ x -> return x
      , tfTyName = \_ -> return False })
