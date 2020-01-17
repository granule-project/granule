module Language.Granule.Synthesis.SplittingSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
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
      res <- runSplitter (TyCon boolId) boolDataCons boolTyCons []  [(xId, Linear (TyCon boolId))]
      res `shouldBe` ([xId], [[PConstr nullSpan () False falseId []], [PConstr nullSpan () False trueId []]])

    -- append : ∀ { a : Type, n m : Nat } . Vec n a → Vec m a → Vec (m + n) a
    -- append x y = {! x y !}
    it "Polymorphic vector append function" $ do
      res <- runSplitter (TyApp (TyApp (TyCon vecId) (TyInfix TyOpPlus (TyVar mId) (TyVar nId))) (TyVar aId)) vecDataCons vecTyCons vecTyVarCtxt [
        (xId, Linear (TyApp (TyApp (TyCon vecId) (TyVar nId)) (TyVar aId))),
        (yId, Linear (TyApp (TyApp (TyCon vecId) (TyVar mId)) (TyVar aId)))
        ]
      res `shouldBe` ([xId, yId], [[PConstr nullSpan () False nilId [], PConstr nullSpan () False nilId []], [PConstr nullSpan () False nilId [], PConstr nullSpan () False consId [PVar nullSpan () False (Id "y.0" "y.0"), PVar nullSpan () False (Id "y.1" "y.1")]], [PConstr nullSpan () False consId [PVar nullSpan () False (Id "x.0" "x.0"), PVar nullSpan () False (Id "x.1" "x.1")], PConstr nullSpan () False nilId []], [PConstr nullSpan () False consId [PVar nullSpan () False (Id "x.0" "x.0"), PVar nullSpan () False (Id "x.1" "x.1")],PConstr nullSpan () False consId [PVar nullSpan () False (Id "y.0" "y.0"), PVar nullSpan () False (Id "y.1" "y.1")]]])

    -- i : ∀ { a : Type } . a → a
    -- i x = {! x !}
    it "Polymorphic identity" $ do
      res <- runSplitter (FunTy Nothing (TyVar aId) (TyVar aId)) [] [] [] [(xId, Linear (TyVar aId))]
      res `shouldBe` ([xId], [[PVar nullSpan () False xId]])

    -- i : ∀ { a : Type } . a → a
    -- i x = {! !}
    it "Empty hole" $ do
      res <- runSplitter (FunTy Nothing (TyVar aId) (TyVar aId)) [] [] [] []
      res `shouldBe` ([], [[]])

    -- k : ∀ { a b : Type } . a → b [0] → a
    -- k x y = {! x y !}
    it "K combinator with 0-graded second parameter" $ do
      res <- runSplitter
        (FunTy Nothing (TyVar aId) (FunTy Nothing (Box (CNat 0) (TyVar bId)) (TyVar aId)))
        [] [] []
        [(xId, Linear (TyVar aId)), (yId, Linear (Box (CNat 0) (TyVar bId)))]
      res `shouldBe` ([xId, yId], [[PVar nullSpan () False xId, PBox nullSpan () False (PVar nullSpan () False yId)]])

    -- o : ∀ { a b c : Type } . (a → b) → (b → c) → (a → c)
    -- o a b c = {! a b c !}
    it "Function composition" $ do
      res <- runSplitter
        (FunTy Nothing (FunTy Nothing (TyVar aId) (TyVar bId)) (FunTy Nothing (FunTy Nothing (TyVar bId) (TyVar cId)) (FunTy Nothing (TyVar aId) (TyVar cId))))
        [] [] []
        [
          (aId, Linear (FunTy Nothing (TyVar aId) (TyVar bId))),
          (bId, Linear (FunTy Nothing (TyVar bId) (TyVar bId))),
          (cId, Linear (TyVar aId))
        ]
      res `shouldBe` ([aId, bId, cId], [
          [PVar nullSpan () False aId,
          PVar nullSpan () False bId,
          PVar nullSpan () False cId]])

    -- f : ∀ { a : Type, n : Nat } . Vec 0 a → Vec 1 a → Vec 2 a
    -- f xs ys = {! xs ys !}
    it "Sized vectors" $ do
      res <- runSplitter
        (TyApp (TyApp (TyCon vecId) (TyInt 2)) (TyVar aId))
        vecDataCons vecTyCons vecTyVarCtxt
        [(xId, Linear (TyApp (TyApp (TyCon vecId) (TyInt 0)) (TyVar aId))),
         (yId, Linear (TyApp (TyApp (TyCon vecId) (TyInt 1)) (TyVar aId)))]
      res `shouldBe` ([xId, yId], [[PConstr nullSpan () False nilId [], PConstr nullSpan () False consId [PVar nullSpan () False (Id "y.0" "y.0"), PVar nullSpan () False (Id "y.1" "y.1")]]])

    -- flip : ∀ { a : Type, b : Type } . (a, b) → (b, a)
    -- flip pair = {! pair !}
    it "Tuples" $ do
      res <- runSplitter
        (TyApp (TyApp (TyCon (Id "," ",")) (TyVar bId)) (TyVar aId))
        tupleDataCons tupleTypeCons [(aId, (KType, ForallQ)),(bId, (KType, ForallQ))]
        [(xId, Linear (TyApp (TyApp (TyCon (Id "," ",")) (TyVar aId)) (TyVar bId)))]
      res `shouldBe` ([xId], [[PConstr nullSpan () False tupleId [PVar nullSpan () False (Id "x.0" "x.0"), PVar nullSpan () False (Id "x.1" "x.1")]]])


boolId, vecId, natId, xId, yId, aId, bId, cId, nId, mId, nilId, consId, trueId, falseId, tupleId :: Id
boolId = mkId "Bool"
vecId = mkId "Vec"
natId = mkId "Nat"
xId = mkId "x"
yId = mkId "y"
aId = mkId "a"
bId = mkId "b"
cId = mkId "c"
nId = mkId "n"
mId = mkId "m"
nilId = mkId "Nil"
consId = mkId "Cons"
trueId = mkId "True"
falseId = mkId "False"
tupleId = mkId ","

boolDataCons :: (?globals :: Globals) => Ctxt (Ctxt (TypeScheme, Substitution))
boolDataCons =
  [(boolId, [(falseId, (Forall nullSpan [] [] (TyCon boolId), [])), (trueId, (Forall nullSpan [] [] (TyCon boolId), []))])]

boolTyCons :: Ctxt (Kind, [Id], Bool)
boolTyCons = [(boolId, (KType, [falseId, trueId], False))]

vecDataCons :: (?globals :: Globals) => Ctxt (Ctxt (TypeScheme, Substitution))
vecDataCons =
  [(vecId, [
    (nilId, (Forall nullSpan [(Id "t1" "t1", KType), (Id "t2" "t2", KType), (Id "t3" "t3", KPromote (TyCon natId))] [] (TyApp (TyApp (TyCon vecId) (TyVar (Id "t3" "t3"))) (TyVar (Id "t2" "t2"))), [(Id "t2" "t2", SubstT (TyVar (Id "t1" "t1"))), (Id "t3" "t3", SubstT (TyInt 0))])),
    (consId, (Forall nullSpan [(nId, KPromote (TyCon natId)), (Id "t4" "t4", KType), (Id "t5" "t5", KType), (Id "t6" "t6", KPromote (TyCon natId))] [] (FunTy Nothing (TyVar (Id "t4" "t4")) (FunTy Nothing (TyApp (TyApp (TyCon vecId) (TyVar nId)) (TyVar (Id "t4" "t4"))) (TyApp (TyApp (TyCon vecId) (TyVar (Id "t6" "t6"))) (TyVar (Id "t5" "t5"))))), [(Id "t5" "t5", SubstT (TyVar (Id "t4" "t4"))), (Id "t6" "t6", SubstT (TyInfix TyOpPlus (TyVar nId) (TyInt 1)))]))
    ])
  ]

vecTyCons :: Ctxt (Kind, [Id], Bool)
vecTyCons = [(vecId, (KFun (KPromote (TyCon natId)) (KFun KType KType), [nilId, consId],True)), (Id "N" "N", (KFun (KPromote (TyCon natId)) KType, [Id "Z" "Z", Id "S" "S"], True)), (natId, (KUnion KCoeffect KEffect,[],False))]

vecTyVarCtxt :: Ctxt (Kind, Quantifier)
vecTyVarCtxt = [(aId, (KType, ForallQ)), (nId, (KPromote (TyCon natId), ForallQ)), (mId, (KPromote (TyCon natId), ForallQ))]

tupleDataCons :: (?globals :: Globals) => Ctxt (Ctxt (TypeScheme, Substitution))
tupleDataCons = [(tupleId, [(tupleId, (Forall nullSpan [(Id "t1" "t1", KType), (Id "t3" "t3", KType), (Id "t2" "t2", KType), (Id "t4" "t4", KType)] [] (FunTy Nothing (TyVar (Id "t1" "t1")) (FunTy Nothing (TyVar (Id "t3" "t3")) (TyApp (TyApp (TyCon (Id "," ",")) (TyVar (Id "t4" "t4"))) (TyVar (Id "t2" "t2"))))),[(Id "t2" "t2", SubstT (TyVar (Id "t3" "t3"))),(Id "t4" "t4", SubstT (TyVar (Id "t1" "t1")))]))])]

tupleTypeCons :: Ctxt (Kind, [Id], Bool)
tupleTypeCons = [(tupleId, (KFun KType (KFun KType KType), [tupleId], False))]

runSplitter :: (?globals :: Globals)
  => Type
  -> Ctxt (Ctxt (TypeScheme, Substitution))
  -> Ctxt (Kind, [Id], Bool)
  -> Ctxt (Kind, Quantifier)
  -> Ctxt Assumption
  -> IO ([Id], [[Pattern ()]])
runSplitter ty dataCons tyCons tyVarCtxt ctxt = do
  let st = initState {
    patternConsumption = repeat NotFull,
    dataConstructors = concatMap snd dataCons,
    typeConstructors = tyCons,
    tyVarContext = tyVarCtxt }
  (Right res, _) <- runChecker st (generateCases nullSpan ty dataCons ctxt)
  return res