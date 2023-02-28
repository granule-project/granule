module Language.Granule.Synthesis.SynthSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test

import Language.Granule.Synthesis.Common
import Language.Granule.Synthesis.Monad
import Language.Granule.Synthesis.Synth
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Variables
import Language.Granule.Checker.Checker(checkDataCons,checkTyCon)
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Utils
import Language.Granule.Synthesis.Contexts

import Control.Monad.State.Strict

-- To run just these tests do:
--  stack test granule-frontend --test-arguments "-m "Synth""

spec :: Test.Spec
spec =
  checkCasePatterns

checkCasePatterns :: Test.Spec
checkCasePatterns = do
  describe "Simple constructor test for Bool" $ do
      let true = Forall ns [] [] (TyCon $ mkId "Bool")
      let nat = TyCon $ mkId "Nat"
      (results, synthData) <- let ?globals = mempty :: Globals in do
          testSynthesiser $ do
              tyVarA <- conv $ freshTyVarInContextWithBinding (mkId "a") (Type 0) ForallQ
              tyVarR <- conv $ freshTyVarInContextWithBinding (mkId "r") nat ForallQ
              tyVarS <- conv $ freshTyVarInContextWithBinding (mkId "s") nat ForallQ
              let var = (mkId "x", SVar (Discharged
                              (TyCon (mkId "Bool"))
                              (TyVar tyVarR)) Nothing)
              let gamma = [(mkId "y", SVar (Discharged (TyVar tyVarA) (TyVar tyVarS)) Nothing)]
              let omega = []

              casePatternMatchBranchSynth
                  defaultSearchParams
                  RightAsync
                  gamma
                  omega
                  var
                  (mkId "Bool")
                  (TyVar tyVarA)
                  (mkId "True", (true, []))

      -- Patter-expr pair
      let patternExprPair = map (fmap fst . fst) results
      it "Branch on (True : Bool) produces expected pattern-expr pair" $ do
        patternExprPair
          `shouldBe` [Just (PConstr ns () False (mkId "True") [], Val ns () False (Var () (mkId "y")))]

      -- Predicate
      it "Branch on (True : Bool) produces expected predicate" $ do
        let predicate = map (fromPredicateContext . predicateContext . snd) results
        let expectedApprox1 = Con $ ApproximatedBy ns (TyVar $ mkId "s") (TyInfix TyOpTimes (TyVar $ mkId "s'") (TyGrade Nothing 1)) nat
        let expectedApprox2 = Con $ ApproximatedBy ns (TyInfix TyOpTimes (TyVar $ mkId "s'") (TyGrade Nothing 1)) (TyInfix TyOpTimes (TyVar $ mkId "r") (TyGrade Nothing 1)) nat
        predicate
          `shouldBe` (Impl [] (Conj []) (ExistsHere "s'" nat (Conj [expectedApprox1, expectedApprox2])))

-- Helper for running the synthesiser
testSynthesiser :: (?globals :: Globals)
  => Synthesiser (Maybe a)
  -> IO ([(Maybe a, CheckerState)], SynthesisData)
testSynthesiser synthComputation = do
    -- Representation of
    -- data Bool = True | False
    let extras =
          [DataDecl {dataDeclSpan = ns
                  , dataDeclId = (Id "Bool" "Bool")
                  , dataDeclTyVarCtxt = []
                  , dataDeclKindAnn = Nothing
                  , dataDeclDataConstrs =
                    [DataConstrNonIndexed {dataConstrSpan = ns
                                          , dataConstrId = (Id "True" "True")
                                          , dataConstrParams = []}
                    ,DataConstrNonIndexed {dataConstrSpan = ns
                                        , dataConstrId = (Id "False" "False")
                                        , dataConstrParams = []}] }]
    -- Load in the primitive data constructors first before running the computation synthComputation
    let synthComputation' =
             (conv (runAll checkTyCon (extras ++ Primitives.dataTypes)))
          >> (conv (runAll checkDataCons (extras ++ Primitives.dataTypes)))
          >> synthComputation
    (outputs, dat) <- runStateT (runSynthesiser 1 synthComputation' initState) mempty
    succeedingOutput <- mapM (\(x, y) -> convertError x >>= (\x' -> return (x', y))) outputs
    return (succeedingOutput, dat)
  where
    convertError (Right a) = return a
    convertError (Left err) = do
      -- Print error message if something went badly wrong
      putStrLn $ show err
      return $ Nothing