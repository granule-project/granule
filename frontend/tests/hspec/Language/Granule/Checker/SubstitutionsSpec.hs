{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.SubstitutionsSpec where

import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Identifiers
import Language.Granule.TestUtils

import Test.Hspec
import Language.Granule.Checker.Substitutions
import Language.Granule.Checker.Monad
import Control.Monad.Trans.Maybe
import Language.Granule.Utils

spec :: Spec
spec = do
  describe "unification" $
    it "unif test" $ do
      let ?globals = defaultGlobals
      Just us <- evalChecker initState $ runMaybeT $
             unify (Box (CVar $ mkId "x") (TyCon $ mkId "Bool"))
                   (Box (COne (TyCon $ mkId "Nat")) (TyVar $ mkId "a"))
      us `shouldBe` (Just [(mkId "x", SubstC $ COne (TyCon $ mkId "Nat"))
                         , (mkId "a", SubstT $ TyCon $ mkId "Bool")])
