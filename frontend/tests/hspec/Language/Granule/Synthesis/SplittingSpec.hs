module Language.Granule.Synthesis.SplittingSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test

import Language.Granule.Checker.Monad
import Language.Granule.Checker.SubstitutionContexts

import Language.Granule.Context

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pattern

import Language.Granule.Synthesis.Splitting

import Language.Granule.Utils

spec :: Test.Spec
spec = let ?globals = mempty in do
  describe "case splitting" $ do
    -- not : Bool → Bool
    -- not x = {! x !}
    it "Boolean not function" $ do
      res <- runSplitter boolConstructors [(xId, Linear (TyCon boolId))]
      res `shouldBe` [(xId, [PConstr nullSpan () falseId [], PConstr nullSpan () trueId []])]

    -- append : ∀ { a : Type, n m : Nat } . Vec n a → Vec m a → Vec (m + n) a
    -- append x y = {! x y !}
    it "Polymorphic vector append function" $ do
      res <- runSplitter vecConstructors [
        (xId, Linear (TyApp (TyApp (TyCon vecId) (TyVar nId)) (TyVar aId))),
        (yId, Linear (TyApp (TyApp (TyCon vecId) (TyVar mId)) (TyVar aId)))
        ]
      res `shouldBe` [
        (xId, [PConstr nullSpan () nilId [], PConstr nullSpan () consId [PVar nullSpan () (Id "x.0" "x.0"), PVar nullSpan () (Id "x.1" "x.1")]]),
        (yId, [PConstr nullSpan () nilId [], PConstr nullSpan () consId [PVar nullSpan () (Id "y.0" "y.0"), PVar nullSpan () (Id "y.1" "y.1")]])
        ]

    -- i : ∀ { a : Type } . a → a
    -- i x = {! x !}
    it "Polymorphic identity" $ do
      res <- runSplitter [] [(xId, Linear (TyVar aId))]
      res `shouldBe` [(xId, [PVar nullSpan () xId])]

    -- k : ∀ { a b : Type } . a → b [0] → a
    -- k x y = {! x y !}
    it "K combinator with 0-graded second parameter" $ do
      res <- runSplitter [] [(xId, Linear (TyVar aId)), (yId, Linear (Box (CNat 0) (TyVar bId)))]
      res `shouldBe` [(xId, [PVar nullSpan () xId]), (yId, [PBox nullSpan () (PVar nullSpan () yId)])]

    -- o : ∀ { a b c : Type } . (a → b) → (b → c) → (a → c)
    -- o a b x = {! a b x !}
    it "Function composition" $ do
      res <- runSplitter [] [
        (aId, Linear (FunTy (TyVar aId) (TyVar bId))),
        (bId, Linear (FunTy (TyVar bId) (TyVar bId))),
        (xId, Linear (TyVar aId))
        ]
      res `shouldBe` [
        (aId, [PVar nullSpan () aId]),
        (bId, [PVar nullSpan () bId]),
        (xId, [PVar nullSpan () xId])
        ]

boolId, vecId, natId, xId, yId, aId, bId, nId, mId, nilId, consId, trueId, falseId :: Id
boolId = mkId "Bool"
vecId = mkId "Vec"
natId = mkId "Nat"
xId = mkId "x"
yId = mkId "y"
aId = mkId "a"
bId = mkId "b"
nId = mkId "n"
mId = mkId "m"
nilId = mkId "Nil"
consId = mkId "Cons"
trueId = mkId "True"
falseId = mkId "False"

boolConstructors :: (?globals :: Globals) => Ctxt (Ctxt (TypeScheme, Substitution))
boolConstructors =
  [(boolId, [(falseId, (Forall nullSpan [] [] (TyCon boolId), [])), (trueId, (Forall nullSpan [] [] (TyCon boolId), []))])]

vecConstructors :: (?globals :: Globals) => Ctxt (Ctxt (TypeScheme, Substitution))
vecConstructors =
  [(vecId, [
    (nilId, (Forall nullSpan [(Id "t1" "t1", KType), (Id "t2" "t2", KType), (Id "t3" "t3", KPromote (TyCon natId))] [] (TyApp (TyApp (TyCon vecId) (TyVar (Id "t3" "t3"))) (TyVar (Id "t2" "t2"))), [(Id "t2" "t2", SubstT (TyVar (Id "t1" "t1"))), (Id "t3" "t3", SubstT (TyInt 0))])),
    (consId, (Forall nullSpan [(nId, KPromote (TyCon natId)), (Id "t4" "t4", KType), (Id "t5" "t5", KType), (Id "t6" "t6", KPromote (TyCon natId))] [] (FunTy (TyVar (Id "t4" "t4")) (FunTy (TyApp (TyApp (TyCon vecId) (TyVar nId)) (TyVar (Id "t4" "t4"))) (TyApp (TyApp (TyCon vecId) (TyVar (Id "t6" "t6"))) (TyVar (Id "t5" "t5"))))), [(Id "t5" "t5", SubstT (TyVar (Id "t4" "t4"))), (Id "t6" "t6", SubstT (TyInfix TyOpPlus (TyVar nId) (TyInt 1)))]))
    ])
  ]


runSplitter :: (?globals :: Globals)
            => Ctxt (Ctxt (TypeScheme, Substitution))
            -> Ctxt Assumption
            -> IO (Ctxt [Pattern ()])
runSplitter constructors ctxt = do
  (Right res, _) <- runChecker initState (generateCases nullSpan constructors ctxt)
  return res