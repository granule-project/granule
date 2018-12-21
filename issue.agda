module Issue where

open import Data.Product
open import Data.Integer
open import Data.Nat hiding (_+_; _≥_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

⟦_⟧ : ℕ -> ℤ
⟦ n ⟧ = + n

postulate
  inj+1 : forall {n m  : ℤ} -> (n + ⟦ 1 ⟧ ≡ m + ⟦ 1 ⟧) -> n ≡ m

propagateAnd : forall {n m : ℤ} {P : ℤ -> Set} -> (n ≡ m × P n) -> P m
propagateAnd (zeron , second) rewrite zeron = second


thm :
 -- n comes from the signature
 -- n' comes from the recursive application in side
 forall (n : ℤ) -> Σ ℤ (\n' ->
   -- pre conditions
   (n ≥ ⟦ 0 ⟧) -> (n' ≥ ⟦ 0 ⟧ ×
    (forall (n0 n4 : ℤ) ->
      ((n4 + ⟦ 1 ⟧ ≡ n + ⟦ 1 ⟧) ×
        ¬ ((n0 ≡ ⟦ 0 ⟧) × ((n0 + ⟦ 1 ⟧) ≡ (n + ⟦ 1 ⟧))))
         -> (n4 ≡ n' + ⟦ 1 ⟧))))
thm n = ⟦ 1 ⟧ , λ pre → {!!} , λ n0 n4 pres →
  let (pre1 , pre2) = pres

      pre1' = inj+1 {n4} {n} pre1
      -- cong (\q -> ¬ q) (propagateAnd {n0} {0} {\n0 -> n0 + 1 ≡ n + 1}
  in {!!}


neq : ¬ (⟦ 1 ⟧ ≡ ⟦ 0 ⟧)
neq ()

lemma : {k : ℤ} -> k ≥ ⟦ 0 ⟧ -> ¬ (⟦ 0 ⟧ ≡ k + ⟦ 1 ⟧)
lemma {+_ zero} (+≤+ m≤n) = λ ()
lemma {+_ (ℕ.suc n)} (+≤+ m≤n) = λ ()
lemma { -[1+_] n} ()

-- Proof that the theorem is false! with 0 as the counterexample
inv : ¬ (forall (n : ℤ) -> Σ ℤ (\n' ->
   -- pre conditions
   (n ≥ ⟦ 0 ⟧) -> (n' ≥ ⟦ 0 ⟧ ×
    (forall (n0 n4 : ℤ) ->
      ((n4 + ⟦ 1 ⟧ ≡ n + ⟦ 1 ⟧) ×
        ¬ ((n0 ≡ ⟦ 0 ⟧) × ((n0 + ⟦ 1 ⟧) ≡ (n + ⟦ 1 ⟧))))
         -> (n4 ≡ n' + ⟦ 1 ⟧)))))
inv x =
 let (n' , p) = x ⟦ 0 ⟧
     (q , q') = p (+≤+ z≤n)
     w = q' ⟦ 1 ⟧ ⟦ 0 ⟧
     w' = w (refl , λ x₁ → neq (proj₁ x₁))
 in lemma {proj₁ (x ⟦ 0 ⟧)} q w'
