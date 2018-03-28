{-# LANGUAGE ImplicitParams #-}

module Checker.SubstitutionsSpec where

import Syntax.Expr
import Test.Hspec
import Checker.Substitutions
import Checker.Monad
import Control.Monad.Trans.Maybe
import Utils

spec :: Spec
spec = do
  describe "unification" $
    it "unif test" $ do
      let ?globals = defaultGlobals
      Just us <- evalChecker initState $ runMaybeT $
             unify (Box (CVar $ mkId "x") (TyCon $ mkId "Bool"))
                   (Box (COne (CConstr $ mkId "Nat")) (TyVar $ mkId "a"))
      us `shouldBe` (Just [(mkId "x", SubstC $ COne (CConstr $ mkId "Nat"))
                         , (mkId "a", SubstT $ TyCon $ mkId "Bool")])
