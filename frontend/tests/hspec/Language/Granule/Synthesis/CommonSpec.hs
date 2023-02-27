module Language.Granule.Synthesis.CommonSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test

import Language.Granule.Synthesis.Common
import Language.Granule.Synthesis.Monad
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
import Language.Granule.Checker.Checker(checkDataCons,checkTyCon)
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.SubstitutionContexts
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Checker.Monad(initState,runAll)
import Language.Granule.Utils

import Control.Monad.State.Strict

-- To run just these tests do:
--  stack test granule-frontend --test-arguments "-m "Common""

spec :: Test.Spec
spec = let ?globals = mempty :: Globals in do
  checkConstructorTests
  recursiveConstructorTests

recursiveConstructorTests :: Test.Spec
recursiveConstructorTests = do
  describe "Tests on isRecursiveCon" $ do
    let listTy = TyApp (TyCon $ mkId "List") (TyVar $ mkId "a")
    let nilTyS  = Forall ns [(mkId "a", Type 0)] [] listTy
    let consTyS = Forall ns [(mkId "a", Type 0)] [] (FunTy Nothing Nothing (TyVar $ mkId "a") (FunTy Nothing Nothing listTy listTy))

    it "Non-recursive constructor of list (Nil)" $ do
      let recNil = isRecursiveCon (mkId "List") (mkId "Nil", (nilTyS, []))
      recNil `shouldBe` False

    it "Recursive constructor of list (Cons)" $ do
      let recCons = isRecursiveCon (mkId "List") (mkId "Cons", (consTyS, []))
      recCons `shouldBe` True

    it "Relevant constructors for List are returned correctly partioned into rec/non-rec" $ do
      let constructors = [(mkId "List", ([(mkId "Nil", (nilTyS, [])), (mkId "Cons", (consTyS, []))], False))]
      let relConstructors = relevantConstructors (mkId "List") constructors
      relConstructors `shouldBe` ([(mkId "Cons", (consTyS, []))],  [(mkId "Nil", (nilTyS, []))])

    it "Non-recursive constructor of Maybe (Just)" $ do
      let maybeTy = TyApp (TyCon $ mkId "Maybe") (TyVar $ mkId "a")
      let justTy = FunTy Nothing Nothing (TyVar $ mkId "a") maybeTy
      let recJust = isRecursiveCon (mkId "Maybe") (mkId "Just", (Forall ns [(mkId "a", Type 0)] [] justTy, []))
      recJust `shouldBe` False

    it "Recursive constructor involving a pair: (SnocList a, a) -> SnocList a " $ do
      let slistTy = TyApp (TyCon $ mkId "SnocList") (TyVar $ mkId "a")
      let sconsTy = FunTy Nothing Nothing (TyApp (TyApp (TyCon $ mkId ",") slistTy) (TyVar $ mkId "a")) slistTy
      let srecCons = isRecursiveCon (mkId "SnocList") (mkId "SCons", (Forall ns [(mkId "a", Type 0)] [] sconsTy, []))
      srecCons `shouldBe` True

checkConstructorTests :: (?globals :: Globals) => Test.Spec
checkConstructorTests =
  describe "Tests on checkConstructor" $ do
    let unitCon = TyCon (mkId "()")
    it "Monomorphic test: unit" $ do
      -- A unit constructor matches a unit goal
      status <- testCheckConstructor
                   $ checkConstructor (Forall ns [] [] unitCon) unitCon []
      status `shouldBe` [Just (True, unitCon)]

    -- A simple constructor with a polymorphic type
    -- MkSimple :: Simple a
    let simpleCon = TyCon $ mkId "Simple"
    let simple = Forall ns [(mkId "a", Type 0)] [] (TyApp simpleCon (TyVar $ mkId "a"))

    it "Polymorphic test: `Simple a` vs () - fail" $ do
      status <- testCheckConstructor $ checkConstructor simple unitCon []
      status `shouldBe` []
    it "Polymorphic test: `Simple a` vs Simple () - success" $ do
      status <- testCheckConstructor $ checkConstructor simple (TyApp simpleCon unitCon) []
      status `shouldBe` [Just (True, TyApp simpleCon unitCon)]

    -- Either constructor
    let eitherCon = TyCon $ mkId "Either"
    let leftConstr =
          Forall ns [(mkId "a", Type 0), (mkId "b", Type 0)] []
                  (FunTy Nothing Nothing (TyVar $ mkId "a") (TyApp (TyApp eitherCon (TyVar $ mkId "a")) (TyVar $ mkId "b")))

    it "Polymorphic test: `a -> Either a b` vs `Either () ()` - success" $ do
      status <- testCheckConstructor $ checkConstructor  leftConstr (TyApp (TyApp eitherCon unitCon) unitCon) []
      status `shouldBe` [Just (True, (TyApp (TyApp eitherCon unitCon) unitCon))]


    -- Vec constructor
    -- TODO complete this example
    -- let vecCon = TyCon $ mkId "Vec"
    -- let consConstr =
    --       Forall (Span {startPos = (5,12), endPos = (5,29), filename = "simple.gr"}) [((Id "n" "n`0"),TyCon (Id "Nat" "Nat"))] [] (FunTy Nothing Nothing (TyVar (Id "a" "a")) (FunTy Nothing Nothing (TyApp (TyApp (TyCon (Id "Vec" "Vec")) (TyVar (Id "n" "n`0"))) (TyVar (Id "a" "a"))) (TyApp (TyApp (TyCon (Id "Vec" "Vec")) (TyInfix TyOpPlus (TyVar (Id "n" "n`0")) (TyGrade Nothing 1)))

    -- it "Polymorphic test: `a -> Vec n a -> Vec n' a` (with n' ~ n + 1) vs `Vec 0 a` - fail" $ do
    --   status <- testCheckConstructor $ checkConstructor either (TyApp (TyApp eitherCon unitCon) unitCon) []
    --   status `shouldBe` [Just True]

    -- it "Polymorphic test: `a -> Vec n a -> Vec n' a` (with n' ~ n + 1) vs `Vec 1 a` - success" $ do
    --   status <- testCheckConstructor $ checkConstructor either (TyApp (TyApp eitherCon unitCon) unitCon) []
    --   status `shouldBe` [Just True]


-- Helper for running checkConstructor specifically
testCheckConstructor :: (?globals :: Globals) => Synthesiser (Bool, Type, [(Type, Maybe Coeffect)], Substitution, Substitution, Pred)
                                              -> IO [Maybe (Bool, Type)]
testCheckConstructor m = do
  constr <- testSynthesiser m
  let status = map (fmap (\(status, ty, _, _, _, _) -> (status, ty))) constr
  return status

-- Helper for running the synthesiser
testSynthesiser :: (?globals :: Globals) => Synthesiser a -> IO [Maybe a]
testSynthesiser synthComputation = do
    -- Representation of
    -- data Simple a = Simple a
    -- data Maybe a = Nothing | Just a
    -- data Vec (n : Nat) (a : Type) where
    --   Nil : Vec 0 a;
    --   Cons : forall {n : Nat} . a -> Vec n a -> Vec (n+1) a
    let extras =
          [DataDecl {dataDeclSpan = Span {startPos = (1,1), endPos = (1,17), filename = "simple.gr"}
                    , dataDeclId = (Id "Simple" "Simple")
                    , dataDeclTyVarCtxt = [((Id "a" "a"),Type 0)]
                    , dataDeclKindAnn = Nothing
                    , dataDeclDataConstrs = [DataConstrNonIndexed {dataConstrSpan = Span {startPos = (1,17), endPos = (1,17), filename = "simple.gr"}
                                            , dataConstrId = (Id "Simple" "Simple")
                                            , dataConstrParams = [TyVar (Id "a" "a")]}]}
         ,DataDecl {dataDeclSpan = Span {startPos = (2,1), endPos = (2,28), filename = "simple.gr"}
                    , dataDeclId = (Id "Either" "Either")
                    , dataDeclTyVarCtxt = [((Id "a" "a"),Type 0),((Id "b" "b"),Type 0)]
                    , dataDeclKindAnn = Nothing
                    , dataDeclDataConstrs = [DataConstrNonIndexed {dataConstrSpan = Span {startPos = (2,19), endPos = (2,19), filename = "simple.gr"}
                                                                  , dataConstrId = (Id "Left" "Left")
                                                                  , dataConstrParams = [TyVar (Id "a" "a")]}
                                            ,DataConstrNonIndexed {dataConstrSpan = Span {startPos = (2,28), endPos = (2,28), filename = "simple.gr"}
                                                                  , dataConstrId = (Id "Right" "Right")
                                                                  , dataConstrParams = [TyVar (Id "b" "b")]}]}
         ,DataDecl {dataDeclSpan = Span {startPos = (3,1), endPos = (5,29), filename = "simple.gr"}, dataDeclId = (Id "Vec" "Vec"), dataDeclTyVarCtxt = [((Id "n" "n"),TyCon (Id "Nat" "Nat")),((Id "a" "a"),Type 0)], dataDeclKindAnn = Nothing, dataDeclDataConstrs = [DataConstrIndexed {dataConstrSpan = Span {startPos = (4,5), endPos = (0,0), filename = "simple.gr"}, dataConstrId = (Id "NilV" "NilV"), dataConstrTypeScheme = Forall (Span {startPos = (0,0), endPos = (0,0), filename = ""}) [] [] (TyApp (TyApp (TyCon (Id "Vec" "Vec")) (TyGrade Nothing 0)) (TyVar (Id "a" "a")))},DataConstrIndexed {dataConstrSpan = Span {startPos = (5,5), endPos = (5,29), filename = "simple.gr"}, dataConstrId = (Id "ConsV" "ConsV"), dataConstrTypeScheme = Forall (Span {startPos = (5,12), endPos = (5,29), filename = "simple.gr"}) [((Id "n" "n`0"),TyCon (Id "Nat" "Nat"))] [] (FunTy Nothing Nothing (TyVar (Id "a" "a")) (FunTy Nothing Nothing (TyApp (TyApp (TyCon (Id "Vec" "Vec")) (TyVar (Id "n" "n`0"))) (TyVar (Id "a" "a"))) (TyApp (TyApp (TyCon (Id "Vec" "Vec")) (TyInfix TyOpPlus (TyVar (Id "n" "n`0")) (TyGrade Nothing 1))) (TyVar (Id "a" "a")))))}]}
         ,DataDecl {dataDeclSpan = Span {startPos = (6,1), endPos = (6,21), filename = "simple.gr"}, dataDeclId = (Id "List" "List"), dataDeclTyVarCtxt = [((Id "a" "a"),Type 0)], dataDeclKindAnn = Nothing, dataDeclDataConstrs = [DataConstrNonIndexed {dataConstrSpan = Span {startPos = (6,15), endPos = (6,15), filename = "simple.gr"}, dataConstrId = (Id "Nil" "Nil"), dataConstrParams = []},DataConstrNonIndexed {dataConstrSpan = Span {startPos = (6,21), endPos = (6,21), filename = "simple.gr"}, dataConstrId = (Id "Cons" "Cons"), dataConstrParams = [TyVar (Id "a" "a"),TyApp (TyCon (Id "List" "List")) (TyVar (Id "a" "a"))]}]}]
    -- Load in the primitive data constructors first before running the computation synthComputation
    let synthComputation' =
             (conv (runAll checkTyCon (extras ++ Primitives.dataTypes)))
          >> (conv (runAll checkDataCons (extras ++ Primitives.dataTypes)))
          >> synthComputation
    (outputs, dat) <- runStateT (runSynthesiser 1 synthComputation' initState) mempty
    mapM (convertError . fst) outputs
  where
    convertError (Right a) = return $ Just a
    convertError (Left err) = do
      -- Print error message if something went badly wrong
      putStrLn $ show err
      return $ Nothing