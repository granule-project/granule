{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.SubstitutionsSpec where

import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers

import Test.Hspec
import Language.Granule.Checker.Substitution
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Utils

spec :: Spec
spec = do
  describe "unification" $
    it "unif test" $ do
      let ?globals = mempty{ globalsTesting = Just True }
      let initState' = initState { tyVarContext = 
             [ (mkId "x", (TyCon $ mkId "Nat", InstanceQ))
             , (mkId "a", (Type 0, InstanceQ)) ] }
      Right us <- evalChecker initState' $
             unify (Box (TyVar $ mkId "x") (TyCon $ mkId "Bool"))
                   (Box (TySig (TyInt 1) (TyCon $ mkId "Nat")) (TyVar $ mkId "a"))
      us `shouldBe` (Just [(mkId "a", SubstT $ TyCon $ mkId "Bool")
                          , (mkId "x", SubstT $ TySig (TyInt 1) (TyCon $ mkId "Nat"))])
