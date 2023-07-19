{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.SubstitutionsSpec where

import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers

import Test.Hspec
import Language.Granule.Checker.Kinding
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Utils

spec :: Spec
spec = do
  describe "unification" $
    it "unif test" $ do
      let ?globals = mempty{ globalsTesting = Just True }
      let initState' =
            initState { typeConstructors = [(mkId "()", (Type 0, [], []))]
                      , tyVarContext =
                        [ (mkId "x", (TyCon $ mkId "Nat", InstanceQ))
                        , (mkId "a", (Type 0, InstanceQ)) ] }
      us <- evalChecker initState' $
             unify (Box (TyVar $ mkId "x") (TyCon $ mkId "()"))
                   (Box (TySig (TyInt 1) (TyCon $ mkId "Nat")) (TyVar $ mkId "a"))
      let result = case us of
                     Right res -> res
                     Left  err -> error $ show err
      result `shouldBe` (Just [(mkId "a", SubstT $ TyCon $ mkId "()")])
