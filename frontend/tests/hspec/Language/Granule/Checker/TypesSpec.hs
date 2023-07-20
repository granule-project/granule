{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.TypesSpec where

import Language.Granule.Syntax.Identifiers
import Test.Hspec
import Language.Granule.Context
import Language.Granule.Checker.DataTypes
import Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Parser
import Language.Granule.Syntax.Type
import Language.Granule.Checker.Kinding
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Types
import Language.Granule.Checker.Monad
import Language.Granule.Utils

import Control.Monad.State.Strict

import Data.Either (fromRight)

spec :: Spec
spec = do
  describe "context handling" $ do
    it "Replacing replaces only one occurence" $
      (replace [(mkId "x", 1), (mkId "y", 2), (mkId "x", 3)] (mkId "x") 0)
        `shouldBe` [(mkId "x", 0), (mkId "y", 2), (mkId "x", 3)]

    it "Check type index recognition behaviour" $ do
      result <- let ?globals = mempty :: Globals in do
        evalChecker initState $ do
          (ast@(AST dataDecls defs imports hidden name), _) <- liftIO $ parseAndFreshenDefs dataNdefinition
          _ <- runAll registerTypeConstructor (Primitives.dataTypes ++ dataDecls)
          _ <- runAll registerDataConstructors (Primitives.dataTypes ++ dataDecls)
          _ <- runAll kindCheckDef defs
          refineBinderQuantification
                    [(mkId "m", tyCon "Nat"), (mkId "a", Type 0)]
                    (FunTy Nothing Nothing (TyApp (tyCon "N") (tyVar "m")) (tyVar "a"))

      -- Binder checks
      let binders = fromRight [] result
      binders `shouldBe` [(mkId "m", (tyCon "Nat", BoundQ)), (mkId "a", (Type 0, ForallQ))]

dataNdefinition :: String
dataNdefinition = "data N (n : Nat) where \n Z : N 0; \n S : forall {n : Nat} . N n -> N (n + 1)"