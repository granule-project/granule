{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}

{-# options_ghc -Wno-missing-pattern-synonym-signatures #-}

module Data.Bifunctor.FoldableSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test
import Data.Bifunctor.Foldable
import Data.Bifunctor.TH

data ExprF expr val =
    AndF expr expr
    | OrF expr expr
    | NotF expr
    | ValF val
    deriving Functor
$(deriveBifunctor ''ExprF)

type Expr = Fix2 ExprF ValueF

pattern And :: Fix2 ExprF g -> Fix2 ExprF g -> Fix2 ExprF g
pattern And l r = (Fix2 (AndF l r))

pattern Or :: Fix2 ExprF g -> Fix2 ExprF g -> Fix2 ExprF g
pattern Or l r = (Fix2 (OrF l r))

pattern Not :: Fix2 ExprF g -> Fix2 ExprF g
pattern Not v = (Fix2 (NotF v))

pattern Val :: Fix2 g ExprF -> Fix2 ExprF g
pattern Val v = (Fix2 (ValF v))

data ValueF val expr =
    LitF Bool
    | IgnoreF expr Bool -- `expr` does nothing, it's just here to
                        -- demonstrate mutual recursion.
    deriving Functor
$(deriveBifunctor ''ValueF)

type Value = Fix2 ValueF ExprF

pattern Lit :: Bool -> Fix2 ValueF g
pattern Lit b = (Fix2 (LitF b))

pattern Ignore :: Fix2 g ValueF -> Bool -> Fix2 ValueF g
pattern Ignore e b = (Fix2 (IgnoreF e b))

spec :: Test.Spec
spec = do
  describe "Mutually Recursive Bifunctors" $
    it "cata works for bools" $
      let expr = (And
                    (Or
                        (Val (Lit True))
                        (Val (Lit False)))
                    (Val
                        (Ignore
                            (Not
                                (Val (Lit True))) False))) :: Expr

      in bicata evalExpr evalVal expr `shouldBe` False
         where evalExpr (AndF l r) = l && r
               evalExpr (OrF l r) = l || r
               evalExpr (NotF v) = not v
               evalExpr (ValF v) = v
               evalExpr :: ExprF Bool Bool -> Bool

               evalVal (LitF v) = v
               evalVal (IgnoreF b r) = r
               evalVal :: ValueF Bool Bool -> Bool
