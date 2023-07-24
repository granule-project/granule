module Language.Granule.Synthesis.SynthSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test

import Language.Granule.Synthesis.Common
import Language.Granule.Synthesis.Monad
import Language.Granule.Synthesis.Synth
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Variables
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.DataTypes
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Utils
import Language.Granule.Synthesis.Contexts

import Control.Monad.State.Strict

-- To run just these tests do:
--  stack test granule-frontend --test-arguments "-m "Synth""

spec :: Test.Spec
spec =
  checkCasePatterns



mkPairTy :: [(Id, Kind)] -> Id -> [Type] -> Type
mkPairTy tyVars tName params = foldr (FunTy Nothing Nothing) (returnTy (TyCon tName) tyVars) params
  where
    returnTy t [] = t
    returnTy t (v:vs) = returnTy (TyApp t ((TyVar . fst) v)) vs



checkCasePatterns :: Test.Spec
checkCasePatterns = let ?globals = (mempty :: Globals) {globalsExtensions = [GradedBase]} in do

  describe "Test for casing on a pair" $ do
      it "Case on (a, b)" $ do
        (results, synthData) <- let ?globals = (mempty :: Globals) {globalsExtensions = [GradedBase]} in do
            testSynthesiser $ do

                tyVarA <- conv $ freshTyVarInContextWithBinding (mkId "a") (Type 0) ForallQ
                tyVarB <- conv $ freshTyVarInContextWithBinding (mkId "b") (Type 0) ForallQ
                x <- freshIdentifier

                Synthesiser $ lift $ lift $ modify (\s -> s { constructors = [(mkId ",", ([(mkId ",", (Forall ns [] [] (mkPairTy [(tyVarA, Type 0),(tyVarB, Type 0)] (mkId ",") [TyVar tyVarA, TyVar tyVarB]) , [] :: Substitution))], False))] })
                let pairTy = TyApp (TyApp (TyCon $ mkId ",") (TyVar tyVarA)) (TyVar tyVarB)
                let grade_r = TyInfix TyOpInterval (TyGrade Nothing 0) (TyGrade Nothing 1)
                let sParams = SearchParams 0 0 0 1 0 10 0
                let var = (x, SVar (Discharged pairTy grade_r) Nothing 0)
                let gamma = []
                let omega = [var]
                let goal = TyVar tyVarA

                (expr, _, _, _, _, _) <- caseRule sParams False LeftAsync gamma (Focused []) (Focused omega) goal
                return (Just expr >>= (\res' -> Just (res', grade_r)))

        let expr = map (fmap fst . fst) results
        expr
          `shouldBe`
            [Just (Case ns () False (Val ns () False (Var () (Id "x" "x")))
              [(PConstr ns () False (Id "," ",")
                [ PVar ns () False (Id "y" "y"),
                  PVar ns () False (Id "z" "z") ] ,(Val ns () False (Var () (Id "y" "y"))))])]

  describe "Simple constructor test for Bool" $ do

      it "Branch on (True : Bool)" $ do
        let true = Forall ns [] [] (TyCon $ mkId "Bool")
        let nat = TyCon $ mkId "Nat"
        (results, synthData) <- let ?globals = (mempty :: Globals) {globalsExtensions = [GradedBase]} in do
            testSynthesiser $ do
                tyVarA <- conv $ freshTyVarInContextWithBinding (mkId "a") (Type 0) ForallQ
                tyVarR <- conv $ freshTyVarInContextWithBinding (mkId "r") nat ForallQ
                tyVarS <- conv $ freshTyVarInContextWithBinding (mkId "s") nat ForallQ
                let var = (mkId "x", SVar (Discharged
                                (TyCon (mkId "Bool"))
                                (TyVar tyVarR)) Nothing 0)
                let gamma = [(mkId "y", SVar (Discharged (TyVar tyVarA) (TyVar tyVarS)) Nothing 0)]
                let omega = []

                casePatternMatchBranchSynth
                    defaultSearchParams
                    False
                    RightAsync
                    gamma
                    omega
                    var
                    (mkId "Bool")
                    (TyVar tyVarA)
                    (mkId "True", (true, []))

        -- Patter-expr pair
        let patternExprPair = map (fmap fst . fst) results
        patternExprPair
            `shouldBe` [Just (PConstr ns () False (mkId "True") [], Val ns () False (Var () (mkId "y")))]

        -- Predicate
        let predicate = map (fromPredicateContext . predicateContext . snd) results
        predicate `shouldBe` [Impl [] (Conj [Conj [],Conj []]) (Conj [Conj [],Conj [],Conj []])]

  describe "Construcor test for Either" $ do
    it "Branch on (Left : a -> Either a b)" $ do
      let right = Forall ns  [((Id "a.3" "a.3"),Type 0)
                            ,((Id "b.3" "b.3"),Type 0)
                            ,((Id "t.10" "t.10"),Type 0)
                            ,((Id "t.11" "t.11"),Type 0)] []
                            (FunTy Nothing Nothing (TyVar (Id "b.3" "b.3")) (TyApp (TyApp (TyCon (Id "Either" "Either")) (TyVar (Id "t.11" "t.11"))) (TyVar (Id "t.10" "t.10"))))
      let nat = TyCon $ mkId "Nat"
      let coerce = [((Id "t.10" "t.10"),SubstT (TyVar (Id "b.3" "b.3"))),((Id "t.11" "t.11"),SubstT (TyVar (Id "a.3" "a.3")))]
      (results, synthData) <- let ?globals = (mempty :: Globals) {globalsExtensions = [GradedBase]} in do
          testSynthesiser $ do
              tyVarA <- conv $ freshTyVarInContextWithBinding (mkId "a") (Type 0) ForallQ
              tyVarB <- conv $ freshTyVarInContextWithBinding (mkId "b") (Type 0) ForallQ
              tyVarR <- conv $ freshTyVarInContextWithBinding (mkId "r") nat ForallQ
              -- Scrutinee
              let eitherAB = TyApp (TyApp (TyCon $ mkId "Either") (TyVar tyVarA)) (TyVar tyVarB)
              let var = (mkId "scrutinee", SVar (Discharged eitherAB (TyVar tyVarR)) Nothing 0)
              let gamma = []
              -- alternate for the test
              -- (mkId "y", SVar (Discharged (TyVar tyVarA) (TyVar tyVarS)) Nothing)]
              let omega = []

              res <- casePatternMatchBranchSynth
                  defaultSearchParams
                  False
                  RightAsync
                  gamma
                  omega
                  var
                  (mkId "Either")
                  (TyVar tyVarB)
                  (mkId "Right", (right, coerce))

              return (res >>= (\res' -> Just (res', tyVarR)))

      -- Patter-expr pair
      let patternExprPair = map (fmap (fst . fst) . fst) results
      patternExprPair
          `shouldBe` [Just (PConstr ns () False (mkId "Right") [PVar ns () False (mkId "x")], Val ns () False (Var () (mkId "x")))]

      -- Predicate
      let predicate = map (fromPredicateContext . predicateContext . snd) results
      case map (fmap snd . fst) results of
        (Just tyVarRId : _) -> do
          let tyVarR = TyVar tyVarRId
          let expectedApprox1 = Con $ ApproximatedBy ns (TyGrade (Just nat) 1) (TyInfix TyOpTimes (TyVar $ mkId "y") tyVarR) nat
          let expectedApprox2 = Con $ ApproximatedBy ns (TyInfix TyOpTimes (TyVar $ mkId "y") tyVarR) (TyInfix TyOpTimes tyVarR tyVarR) nat
          let lub = Lub ns (TyVar $ mkId "y") (TyVar $ mkId "y") (TyVar $ mkId "ub0") (TyCon $ mkId "Nat") True
          -- ((T ∧ T) -> T ∧ ∃ y : Nat . ((1 : Nat) = y * r0) ∧ (y * r0 = r0 * r0))
          pretty predicate
            `shouldBe` pretty [Impl [] (Conj [Conj [],Conj []])
                              (Conj [
                                  Exists (mkId "y") nat (Conj [Conj [], Conj [], Con lub, expectedApprox1, expectedApprox2])])]
        _ -> fail "Not expected"

-- Helper for running the synthesiser
testSynthesiser :: (?globals :: Globals)
  => Synthesiser (Maybe a)
  -> IO ([(Maybe a, CheckerState)], SynthesisData)
testSynthesiser synthComputation = do
    -- Representation of
    -- data Bool = True | False
    -- data Either a b = Left a | Right b
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
                                        , dataConstrParams = []}] }
            ,DataDecl {dataDeclSpan = ns
                    , dataDeclId = (Id "Either" "Either")
                    , dataDeclTyVarCtxt = [((Id "a" "a"),Type 0),((Id "b" "b"),Type 0)]
                    , dataDeclKindAnn = Nothing
                    , dataDeclDataConstrs = [DataConstrNonIndexed {dataConstrSpan = ns
                                                                  , dataConstrId = (Id "Left" "Left")
                                                                  , dataConstrParams = [TyVar (Id "a" "a")]}
                                            ,DataConstrNonIndexed {dataConstrSpan = ns
                                                                  , dataConstrId = (Id "Right" "Right")
                                                                  , dataConstrParams = [TyVar (Id "b" "b")]}]}]
    -- Load in the primitive data constructors first before running the computation synthComputation
    let synthComputation' =
            --  (conv (runAll checkTyCon (extras ++ Primitives.dataTypes)))
            (conv (runAll registerTypeConstructor (extras ++ Primitives.dataTypes)))
          >> (conv (runAll registerDataConstructors (extras ++ Primitives.dataTypes)))
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