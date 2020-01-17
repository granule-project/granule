{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.CheckerSpec where

import Test.Hspec

import Language.Granule.Checker.Checker
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Monad
import Language.Granule.Syntax.Parser
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Annotated
import Language.Granule.Utils


spec :: Spec
spec = let ?globals = mempty in do
    let tyVarK = TyVar $ mkId "k"
    let varA = mkId "a"

    -- Unit tests
    describe "joinCtxts" $ do
     it "join ctxts with discharged assumption in both" $ do
       ((c, tyVars), pred) <- runCtxts joinCtxts
              [(varA, Discharged tyVarK (CSig (CNat 5) natInterval))]
              [(varA, Discharged tyVarK (cNatOrdered 10))]

       c `shouldBe` [(varA, Discharged tyVarK (CVar (mkId "a.0")))]
       tyVars `shouldBe` [(mkId "a.0", promoteTypeToKind $ natInterval)]
       pred `shouldBe`
        [Conj [Con (Lub nullSpan (cNatOrdered 5) (cNatOrdered 10) (CVar (mkId "a.0")) natInterval)]]
         --[Conj [Con (ApproximatedBy nullSpan (cNatOrdered 10) (CVar (mkId "a.0")) natInterval)
         --     , Con (ApproximatedBy nullSpan (cNatOrdered 5) (CVar (mkId "a.0")) natInterval)]]

     it "join ctxts with discharged assumption in one" $ do
       ((c, _), pred) <- runCtxts joinCtxts
                          [(varA, Discharged (tyVarK) (cNatOrdered 5))]
                          []
       c `shouldBe` [(varA, Discharged (tyVarK) (CVar (mkId "a.0")))]
       pred `shouldBe`
         [Conj [Con (Lub nullSpan (cNatOrdered 5) (CZero natInterval) (CVar (mkId "a.0")) natInterval)]]
         -- [Conj [Con (ApproximatedBy nullSpan (CZero natInterval) (CVar (mkId "a.0")) natInterval)
         --      ,Con (ApproximatedBy nullSpan (cNatOrdered 5) (CVar (mkId "a.0")) natInterval)]]


    describe "intersectCtxtsWithWeaken" $ do
      it "contexts with matching discharged variables" $ do
         (c, _) <- (runCtxts intersectCtxtsWithWeaken)
                 [(varA, Discharged (tyVarK) (cNatOrdered 5))]
                 [(varA, Discharged (tyVarK) (cNatOrdered 10))]
         c `shouldBe`
                 [(varA, Discharged (tyVarK) (cNatOrdered 5))]

      it "contexts with matching discharged variables" $ do
         (c, _) <- (runCtxts intersectCtxtsWithWeaken)
                 [(varA, Discharged (tyVarK) (cNatOrdered 10))]
                 [(varA, Discharged (tyVarK) (cNatOrdered 5))]
         c `shouldBe`
                 [(varA, Discharged (tyVarK) (cNatOrdered 10))]

      it "contexts with matching discharged variables" $ do
         (c, preds) <- (runCtxts intersectCtxtsWithWeaken)
                 [(varA, Discharged (tyVarK) (cNatOrdered 5))]
                 []
         c `shouldBe`
                 [(varA, Discharged (tyVarK) (cNatOrdered 5))]

      it "contexts with matching discharged variables (symm)" $ do
         (c, _) <- (runCtxts intersectCtxtsWithWeaken)
                 []
                 [(varA, Discharged (tyVarK) (cNatOrdered 5))]
         c `shouldBe`
                 [(varA, Discharged (tyVarK) (CZero
                     (TyApp (TyCon $ mkId "Interval") (TyCon $ mkId "Nat"))))]


    describe "elaborator tests" $
      it "simple elaborator tests" $ do
        -- Simple definitions
        -- \x -> x + 1
        (AST _ (def1:_) _ _ _) <- parseAndDoImportsAndFreshenDefs "foo : Int -> Int\nfoo x = x + 1"
        (Right defElab, _) <- runChecker initState (checkDef [] def1)
        annotation (extractMainExpr defElab) `shouldBe` (TyCon $ mkId "Int")

extractMainExpr :: Def v a -> Expr v a
extractMainExpr (Def _ _ [(Equation _ _ _ _ e)] _) = e
extractMainExpr _ = undefined

runCtxts
  :: (?globals::Globals)
  => (Span -> a -> a -> Checker b)
  -> a
  -> a
  -> IO (b, [Pred])
runCtxts f a b = do
  (Right res, state) <- runChecker initState (f nullSpan a b)
  pure (res, predicateStack state)

cNatOrdered  :: Int -> Coeffect
cNatOrdered x = CSig (CNat x) natInterval

natInterval :: Type
natInterval = TyApp (TyCon $ mkId "Interval") (TyCon $ mkId "Nat")

