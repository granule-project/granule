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

import Control.Monad.State.Strict


import Language.Granule.Utils


-- An SAssumption is an assumption used for synthesis: 
--  * It is either a standard Granule assumption OR
--  * a top level definition (with a possible restriction on use, given by a coeffect)
data SAssumption = 
      SVar Assumption (Maybe StructInfo) 
    | SDef TypeScheme (Maybe Coeffect)
  deriving (Show)



newtype FocusedCtxt a = Focused (Ctxt a)


-- A structurally decreasing type is a recursive instance of a recursive data
-- type. For example in the list data type: 
-- List a = Next (List a) | Empty
-- the (List a) to the left of the equals is structurally decreasing, while 
-- the Empty is not. Likewise the Next (List a) is also not decreasing. 
data StructInfo =  NonDecreasing | Decreasing Int
  deriving (Show, Eq, Ord)


isDecr :: Maybe StructInfo -> Bool
isDecr (Just Decreasing{}) = True 
isDecr _ = False 



ctxtSubtract :: (?globals :: Globals) => Ctxt SAssumption  -> Ctxt SAssumption -> Synthesiser (Ctxt SAssumption)
ctxtSubtract gam [] = return gam
ctxtSubtract gam ((x, SVar (Linear t) _):del) =
  case lookupAndCutout x gam of
    Just (gam', _) -> ctxtSubtract gam' del
    Nothing -> none

ctxtSubtract gam ((x, SVar (Discharged t g2) _):del) =
  case lookupAndCutout x gam of
    Just (gam', SVar (Discharged t2 g1) sInf) -> do
      g3 <- g1 `gradeSub` g2
      ctx <- ctxtSubtract gam' del
      return ((x, SVar (Discharged t g3) sInf):ctx)
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

ctxtMultByCoeffect :: Type -> Ctxt SAssumption -> Synthesiser (Ctxt SAssumption)
ctxtMultByCoeffect _ [] = return []
ctxtMultByCoeffect g1 ((x, SVar (Discharged t g2) sInf):xs) = do
  ctxt <- ctxtMultByCoeffect g1 xs
  return ((x, SVar (Discharged t (TyInfix TyOpTimes g1 g2)) sInf): ctxt)

ctxtMultByCoeffect g1 (var@(x, SDef tySch (Just g2)):xs) = do 
  ctxt <- ctxtMultByCoeffect g1 xs 
  return $ (x, SDef tySch (Just $ TyInfix TyOpTimes g1 g2)):ctxt
ctxtMultByCoeffect g (var@(x, SDef tySch Nothing):xs) = do 
  ctxt <- ctxtMultByCoeffect g xs 
  return $ var:ctxt

ctxtMultByCoeffect _ _ = none

ctxtDivByCoeffect :: (?globals :: Globals) => Type -> Ctxt SAssumption -> Synthesiser (Ctxt SAssumption)
ctxtDivByCoeffect _ [] = return []
ctxtDivByCoeffect g1 ((x, SVar (Discharged t g2) sInf):xs) =
    do
      ctxt <- ctxtDivByCoeffect g1 xs
      var <- gradeDiv g1 g2
      return ((x, SVar (Discharged t var) sInf): ctxt)
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

ctxtMerge :: (?globals :: Globals)
          => (Type -> Type -> Type) -- lattice operator
          -> Ctxt SAssumption 
          -> Ctxt SAssumption 
          -> Synthesiser (Ctxt SAssumption)

-- Base cases
--  * Empties
ctxtMerge _ [] [] = return []

--  * Can meet/join an empty context to one that has graded assumptions
ctxtMerge operator [] ((x, SVar (Discharged t g) sInf) : ctxt) = do
  -- Left context has no `x`, so assume it has been weakened (0 gade)
  ctxt' <- ctxtMerge operator [] ctxt
  return $ (x, SVar (Discharged t g) sInf) : ctxt'
--  return $ (x, Discharged t (operator (TyGrade (Just kind) 0) g)) : ctxt'

--  * Cannot meet/join an empty context to one with linear assumptions
ctxtMerge operator [] ((x, SVar (Linear t) sInf) : ctxt) = do
  ctxt' <- ctxtMerge operator [] ctxt
  return $ ((x, SVar (Linear t) sInf) : ctxt')
  
ctxtMerge operator [] (var@(x, SDef tySch g) : ctxt) = do 
  ctxt' <- ctxtMerge operator [] ctxt
  return $ var : ctxt'


-- Inductive cases
ctxtMerge operator ((x, SVar (Discharged t1 g1) sInf) : ctxt1') ctxt2 =
  case lookupAndCutout x ctxt2 of
    Just (ctxt2', SVar (Discharged t2 g2) sInf') ->
      if t1 == t2 -- Just in case but should always be true
        then do
          ctxt' <- ctxtMerge operator ctxt1' ctxt2'
          return $ (x, SVar (Discharged t1 (operator g1 g2)) sInf') : ctxt'
        else none

    Just (_, SVar (Linear _) _) -> none -- mode mismatch
    Just (_, SDef{}) -> none -- mode mismatch

    Nothing -> do
      -- Right context has no `x`, so assume it has been weakened (0 gade)
      ctxt' <- ctxtMerge operator ctxt1' ctxt2
      return $ (x, SVar (Discharged t1 g1) sInf) : ctxt'
      --return $ (x, Discharged t1 (operator g1 (TyGrade (Just kind) 0))) : ctxt'

ctxtMerge operator ((x, SVar (Linear t1) sInf) : ctxt1') ctxt2 =
  case lookupAndCutout x ctxt2 of
    Just (ctxt2', SVar (Linear t2) sInf') ->
      if t1 == t2 -- Just in case but should always be true
        then do
          ctxt' <- ctxtMerge operator ctxt1' ctxt2'
          return $ (x, SVar (Linear t1) sInf') : ctxt1'
        else none

    Just (_, SVar (Discharged{}) _) -> none -- mode mismatch
    Just (_, SDef{}) -> none -- mode mismatch
    Nothing -> none                     -- Cannot weaken a linear thing

ctxtMerge operator (var@(x, SDef tySch (Just g)) : ctxt1') ctxt2 = 
  case lookupAndCutout x ctxt2 of 
    Just (ctxt2', SDef tySch' (Just g')) -> do 
      ctxt' <- ctxtMerge operator ctxt1' ctxt2' 
      return $ (x, SDef tySch (Just $ operator g g')) :ctxt'

ctxtMerge operator (var@(x, SDef tySch Nothing) : ctxt1') ctxt2 = do
    ctxt' <- ctxtMerge operator ctxt1' ctxt2
    return $ var:ctxt'
      





ctxtAdd :: Ctxt SAssumption -> Ctxt SAssumption -> Maybe (Ctxt SAssumption)
ctxtAdd [] y = Just y
ctxtAdd ((x, SVar (Discharged t1 g1) sInf):xs) ys =
  case lookupAndCutout x ys of
    Just (ys', SVar (Discharged t2 g2) sInf') -> do
      ctxt <- ctxtAdd xs ys'
      return $ (x, SVar (Discharged t1 (TyInfix TyOpPlus g1 g2)) sInf') : ctxt
    Nothing -> do
      ctxt <- ctxtAdd xs ys
      return $ (x, SVar (Discharged t1 g1) sInf) : ctxt
    _ -> Nothing
ctxtAdd ((x, SVar (Linear t1) sInf):xs) ys =
  case lookup x ys of
    Just (SVar (Linear t2) sInf') -> Nothing
    Nothing -> do
      ctxt <- ctxtAdd xs ys
      return $ (x, (SVar (Linear t1) sInf)) : ctxt
    _ -> Nothing
ctxtAdd (var@(x, SDef tySch Nothing):xs) ys = do 
  ctxt <- ctxtAdd xs ys 
  return $ var:ctxt
ctxtAdd (var@(x, SDef tySch (Just g1)):xs) ys = 
  case lookupAndCutout x ys of 
    Just (ys', SDef tySch' (Just g1')) -> do 
      ctxt <- ctxtAdd xs ys' 
      return $ (x, SDef tySch (Just $ TyInfix TyOpPlus g1 g1')) : ctxt
    _ -> Nothing