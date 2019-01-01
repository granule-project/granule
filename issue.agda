module Issue where

open import Data.Product
open import Data.Integer
open import Data.Nat hiding (_+_; _≥_)
open import Data.Sum

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

⟦_⟧ : ℕ -> ℤ
⟦ n ⟧ = + n

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
 let (n' , p) = x ⟦ 0 ⟧ -- n = 0 as counter example
     (q , q') = p (+≤+ z≤n)
     w = q' ⟦ 1 ⟧ ⟦ 0 ⟧
     w' = w (refl , λ x₁ → neq (proj₁ x₁))
 in lemma {proj₁ (x ⟦ 0 ⟧)} q w'

-----------------------------------------------------------
