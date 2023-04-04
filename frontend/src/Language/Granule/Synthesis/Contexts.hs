{-# OPTIONS_GHC -Wno-incomplete-patterns #-}


{-# options_ghc -fno-warn-incomplete-uni-patterns #-}
module Language.Granule.Synthesis.Contexts where

import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span

import Language.Granule.Context

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Kinding
import Language.Granule.Checker.Variables
    ( freshIdentifierBase, freshTyVarInContext )
import Language.Granule.Synthesis.Monad
import Language.Granule.Synthesis.Common

import Control.Monad.State.Strict


import Language.Granule.Utils
import Language.Granule.Checker.Coeffects (getGradeFromArrow)




tyAndGrade :: SAssumption -> Maybe (Type, Coeffect)
tyAndGrade (SVar (Discharged ty g) _ _) = Just (ty, g)
tyAndGrade (SDef (Forall _ _ _ ty) g _) = Just (ty, getGradeFromArrow g)
tyAndGrade _ = Nothing 


newtype FocusedCtxt a = Focused (Ctxt a)




isDecr :: Maybe StructInfo -> Bool
isDecr (Just Decreasing{}) = True
isDecr _ = False



ctxtSubtract :: (?globals :: Globals) => Ctxt SAssumption  -> Ctxt SAssumption -> Synthesiser (Ctxt SAssumption)
ctxtSubtract gam [] = return gam
ctxtSubtract gam ((x, SVar (Linear t) _ _):del) =
  case lookupAndCutout x gam of
    Just (gam', _) -> ctxtSubtract gam' del
    Nothing -> none

ctxtSubtract gam ((x, SVar (Discharged t g2) _ _):del) =
  case lookupAndCutout x gam of
    Just (gam', SVar (Discharged t2 g1) sInf depth) -> do
      g3 <- g1 `gradeSub` g2
      ctx <- ctxtSubtract gam' del
      return ((x, SVar (Discharged t g3) sInf depth):ctx)
    _ -> none
    where
      gradeSub g g' = do
        -- g - g' = c
        -- therefore
        -- g = c + g'
        (kind, _, _) <- conv $ synthKind nullSpan g
        var <- conv $ freshTyVarInContext (mkId "c") kind
        conv $ existentialTopLevel var kind
        s <- conv get
        -- modifyPred s $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar var) g') g kind) (predicateContext s)
        -- maximality
        varOther' <- conv $ freshIdentifierBase "cOther"
        let varOther = mkId varOther'
        conv $ addPredicate (Impl [(varOther, kind)]
                                (Conj [Con $ ApproximatedBy nullSpanNoFile (TyInfix TyOpPlus (TyVar varOther) g') g kind])
                                (Conj [Con $ ApproximatedBy nullSpanNoFile (TyVar varOther) (TyVar var) kind]))
        return $ TyVar var
-- Skip over top level defs
ctxtSubtract gam (var@(x, SDef{}):del) = do
  ctxt <- ctxtSubtract gam del
  return $ var:ctxt

ctxtMultByCoeffect :: (?globals :: Globals) => Type -> Ctxt SAssumption -> Synthesiser (Ctxt SAssumption)
ctxtMultByCoeffect _ [] = return []
ctxtMultByCoeffect g1 ((x, SVar (Discharged t g2) sInf depth):xs) = do
  ctxt <- ctxtMultByCoeffect g1 xs
  return ((x, SVar (Discharged t (TyInfix TyOpTimes g1 g2)) sInf depth): ctxt)

ctxtMultByCoeffect g1 (var@(x, SDef tySch (Just g2) depth):xs) = do
  ctxt <- ctxtMultByCoeffect g1 xs
  return $ (x, SDef tySch (Just $ TyInfix TyOpTimes g1 g2) depth):ctxt
ctxtMultByCoeffect g (var@(x, SDef tySch Nothing depth):xs) = do
  ctxt <- ctxtMultByCoeffect g xs
  return $ var:ctxt

ctxtMultByCoeffect _ _ = none

ctxtDivByCoeffect :: (?globals :: Globals) => Type -> Ctxt SAssumption -> Synthesiser (Ctxt SAssumption)
ctxtDivByCoeffect _ [] = return []
ctxtDivByCoeffect g1 ((x, SVar (Discharged t g2) sInf depth):xs) =
    do
      ctxt <- ctxtDivByCoeffect g1 xs
      var <- gradeDiv g1 g2
      return ((x, SVar (Discharged t var) sInf depth): ctxt)
  where
    gradeDiv g g' = do
      (kind, _, _) <- conv $ synthKind nullSpan g
      var <- conv $ freshTyVarInContext (mkId "c") kind
      conv $ existentialTopLevel var kind
      s <- conv get
      -- modifyPred s $ addConstraintViaConjunction (ApproximatedBy nullSpanNoFile (TyInfix TyOpTimes g (TyVar var)) g' kind) (predicateContext s)
      return $ TyVar var

-- Skip over top level defs
ctxtDivByCoeffect g1 (var@(x, SDef{}):xs) = do
  ctxt <- ctxtDivByCoeffect  g1 xs
  return $ var:ctxt

ctxtDivByCoeffect _ _ = none

-- Version of `ctxtMerge` that takes a pure lattice
-- operation
ctxtMergeFromPure :: (?globals :: Globals)
          => (Type -> Type -> Type) -- lattice operator
          -> Ctxt SAssumption
          -> Ctxt SAssumption
          -> Synthesiser (Ctxt SAssumption)
ctxtMergeFromPure f = ctxtMerge (\x y -> return (f x y))

-- Given two contexts, merge them based on some (effectful)
-- lattice operation.
ctxtMerge :: (?globals :: Globals)
          => (Type -> Type -> Synthesiser Type) -- lattice operator
          -> Ctxt SAssumption
          -> Ctxt SAssumption
          -> Synthesiser (Ctxt SAssumption)

-- Base cases
--  * Empties
ctxtMerge _ [] [] = return []

--  * Can meet/join an empty context to one that has graded assumptions
ctxtMerge operator [] ((x, SVar (Discharged t g) sInf depth) : ctxt) = do
  -- Left context has no `x`, so assume it has been weakened (0 gade)
  ctxt' <- ctxtMerge operator [] ctxt
  return $ (x, SVar (Discharged t g) sInf depth) : ctxt'
--  return $ (x, Discharged t (operator (TyGrade (Just kind) 0) g)) : ctxt'

--  * Cannot meet/join an empty context to one with linear assumptions
ctxtMerge operator [] ((x, SVar (Linear t) sInf depth) : ctxt) = do
  ctxt' <- ctxtMerge operator [] ctxt
  return $ ((x, SVar (Linear t) sInf depth) : ctxt')

ctxtMerge operator [] (var@(x, SDef tySch g depth) : ctxt) = do
  ctxt' <- ctxtMerge operator [] ctxt
  return $ var : ctxt'


-- Inductive cases
ctxtMerge operator ((x, SVar (Discharged t1 g1) sInf depth) : ctxt1') ctxt2 =
  case lookupAndCutout x ctxt2 of
    Just (ctxt2', SVar (Discharged t2 g2) sInf' depth) ->
      if t1 == t2 -- Just in case but should always be true
        then do
          ctxt' <- ctxtMerge operator ctxt1' ctxt2'
          merged <- operator g1 g2
          return $ (x, SVar (Discharged t1 merged) sInf' depth) : ctxt'
        else none

    Just (_, SVar (Linear _) _ _) -> none -- mode mismatch
    Just (_, SDef{}) -> none -- mode mismatch

    Nothing -> do
      -- Right context has no `x`, so assume it has been weakened (0 gade)
      ctxt' <- ctxtMerge operator ctxt1' ctxt2
      return $ (x, SVar (Discharged t1 g1) sInf depth) : ctxt'
      --return $ (x, Discharged t1 (operator g1 (TyGrade (Just kind) 0))) : ctxt'

ctxtMerge operator ((x, SVar (Linear t1) sInf depth) : ctxt1') ctxt2 =
  case lookupAndCutout x ctxt2 of
    Just (ctxt2', SVar (Linear t2) sInf' depth) ->
      if t1 == t2 -- Just in case but should always be true
        then do
          ctxt' <- ctxtMerge operator ctxt1' ctxt2'
          return $ (x, SVar (Linear t1) sInf' depth) : ctxt1'
        else none

    Just (_, SVar (Discharged{}) _ _) -> none -- mode mismatch
    Just (_, SDef{}) -> none -- mode mismatch
    Nothing -> none                     -- Cannot weaken a linear thing

ctxtMerge operator (var@(x, SDef tySch (Just g) depth) : ctxt1') ctxt2 =
  case lookupAndCutout x ctxt2 of
    Just (ctxt2', SDef tySch' (Just g') depth) -> do
      ctxt' <- ctxtMerge operator ctxt1' ctxt2'
      merged <- operator g g'
      return $ (x, SDef tySch (Just merged) depth) :ctxt'

ctxtMerge operator (var@(x, SDef tySch Nothing depth) : ctxt1') ctxt2 = do
    ctxt' <- ctxtMerge operator ctxt1' ctxt2
    return $ var:ctxt'






ctxtAdd :: Ctxt SAssumption -> Ctxt SAssumption -> Maybe (Ctxt SAssumption)
ctxtAdd [] y = Just y
ctxtAdd ((x, SVar (Discharged t1 g1) sInf depth):xs) ys =
  case lookupAndCutout x ys of
    Just (ys', SVar (Discharged t2 g2) sInf' depth) -> do
      ctxt <- ctxtAdd xs ys'
      return $ (x, SVar (Discharged t1 (TyInfix TyOpPlus g1 g2)) sInf' depth) : ctxt
    Nothing -> do
      ctxt <- ctxtAdd xs ys
      return $ (x, SVar (Discharged t1 g1) sInf depth) : ctxt
    _ -> Nothing
ctxtAdd ((x, SVar (Linear t1) sInf depth):xs) ys =
  case lookup x ys of
    Just (SVar (Linear t2) sInf' depth) -> Nothing
    Nothing -> do
      ctxt <- ctxtAdd xs ys
      return $ (x, (SVar (Linear t1) sInf depth)) : ctxt
    _ -> Nothing
ctxtAdd (var@(x, SDef tySch Nothing depth):xs) ys = do
  ctxt <- ctxtAdd xs ys
  return $ var:ctxt
ctxtAdd (var@(x, SDef tySch (Just g1) depth):xs) ys =
  case lookupAndCutout x ys of
    Just (ys', SDef tySch' (Just g1') depth) -> do
      ctxt <- ctxtAdd xs ys'
      return $ (x, SDef tySch (Just $ TyInfix TyOpPlus g1 g1') depth) : ctxt
    _ -> Nothing