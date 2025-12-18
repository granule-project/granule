{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.KindSpec where

import Test.Hspec

import Control.Monad.State.Strict

import Language.Granule.Checker.Kinding
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Checker.DataTypes
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type

import Data.List (sort)

spec :: Spec
spec = let ?globals = mempty in do
  describe "typeVarsOfKind" $ do

    it "extracts type variables of kind Type from a simple type" $ do
      result <- evalChecker initState $ do
        -- Register primitives
        _ <- runAll registerTypeConstructor Primitives.dataTypes
        _ <- runAll registerDataConstructors Primitives.dataTypes
        -- Add type variable 'a' with kind Type to context
        let var = mkId "a"
        modify (\st -> st { tyVarContext = [(var, (Type 0, ForallQ))] })
        -- Extract type vars of kind Type from `a -> a`
        typeVarsOfKind (FunTy Nothing Nothing (TyVar var) (TyVar var)) (Type 0) 
      case result of
        Right vars -> sort vars `shouldBe` [mkId "a"]
        Left err -> expectationFailure $ "Checker failed: " ++ show err

    it "extracts multiple type variables of kind Type" $ do
      result <- evalChecker initState $ do
        _ <- runAll registerTypeConstructor Primitives.dataTypes
        _ <- runAll registerDataConstructors Primitives.dataTypes
        -- Add type variables with kind Type
        modify (\st -> st { tyVarContext = [ (mkId "a", (Type 0, ForallQ))
                                           , (mkId "b", (Type 0, ForallQ)) ] })
        typeVarsOfKind (FunTy Nothing Nothing (TyVar (mkId "a")) (TyVar (mkId "b"))) (Type 0) 
      case result of
        Right vars -> sort vars `shouldBe` sort [mkId "a", mkId "b"]
        Left err -> expectationFailure $ "Checker failed: " ++ show err

    it "returns empty list when no type variables match the kind" $ do
      result <- evalChecker initState $ do
        _ <- runAll registerTypeConstructor Primitives.dataTypes
        _ <- runAll registerDataConstructors Primitives.dataTypes
        -- Add type variable with kind Nat (not Type)
        modify (\st -> st { tyVarContext = [(mkId "n", (tyCon "Nat", BoundQ))] })
        typeVarsOfKind (TyVar (mkId "n")) (tyCon "Q") 
      case result of
        Right vars -> vars `shouldBe` []
        Left err -> expectationFailure $ "Checker failed: " ++ show err

    it "extracts type variables from nested types" $ do
      result <- evalChecker initState $ do
        _ <- runAll registerTypeConstructor Primitives.dataTypes
        _ <- runAll registerDataConstructors Primitives.dataTypes
        modify (\st -> st { tyVarContext = [ (mkId "a", (Type 0, ForallQ))
                                           , (mkId "b", (Type 0, ForallQ))
                                           , (mkId "c", (Type 0, ForallQ)) ] })
        -- Type: (a -> b) -> c
        let nestedTy = FunTy Nothing Nothing 
                         (FunTy Nothing Nothing (tyVar "a") (tyVar "b"))
                         (tyVar "c")
        typeVarsOfKind nestedTy (Type 0) 
      case result of
        Right vars -> sort vars `shouldBe` sort [mkId "a", mkId "b", mkId "c"]
        Left err -> expectationFailure $ "Checker failed: " ++ show err

    it "handles Box types correctly" $ do
      result <- evalChecker initState $ do
        _ <- runAll registerTypeConstructor Primitives.dataTypes
        _ <- runAll registerDataConstructors Primitives.dataTypes
        modify (\st -> st { tyVarContext = [(mkId "a", (Type 0, ForallQ))] })
        -- Type: Box r a (simplified - just checking a is found inside Box)
        let boxTy = Box (TyInt 1) (tyVar "a")
        typeVarsOfKind boxTy (Type 0) 
      case result of
        Right vars -> vars `shouldBe` [mkId "a"]
        Left err -> expectationFailure $ "Checker failed: " ++ show err

    it "handles TyApp correctly" $ do
      result <- evalChecker initState $ do
        _ <- runAll registerTypeConstructor Primitives.dataTypes
        _ <- runAll registerDataConstructors Primitives.dataTypes
        modify (\st -> st { tyVarContext = [(mkId "a", (Type 0, ForallQ))] })
        -- Type: Maybe a (as TyApp (TyCon Maybe) (TyVar a))
        let maybeATy = TyApp (tyCon "Maybe") (tyVar "a")
        typeVarsOfKind maybeATy (Type 0)
      case result of
        Right vars -> vars `shouldBe` [mkId "a"]
        Left err -> expectationFailure $ "Checker failed: " ++ show err

    it "filters type variables by kind when mixed kinds present" $ do
      result <- evalChecker initState $ do
        _ <- runAll registerTypeConstructor Primitives.dataTypes
        _ <- runAll registerDataConstructors Primitives.dataTypes
        -- Mix of Type and Nat kinded variables
        modify (\st -> st { tyVarContext = [ (mkId "a", (Type 0, ForallQ))
                                           , (mkId "n", (tyCon "Nat", BoundQ))
                                           , (mkId "b", (Type 0, ForallQ)) ] })
        -- Type that mentions all three: a -> N n -> b
        let mixedTy = FunTy Nothing Nothing (tyVar "a") 
                        (FunTy Nothing Nothing (TyApp (tyCon "N") (tyVar "n")) (tyVar "b"))
        typeVarsOfKind mixedTy (Type 0) 
      case result of
        Right vars -> sort vars `shouldBe` sort [mkId "a", mkId "b"]
        Left err -> expectationFailure $ "Checker failed: " ++ show err
