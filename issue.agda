module Issue where

open import Data.Product
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

postulate
  inj+1 : forall {n m  : ℕ} -> (n + 1 ≡ m + 1) -> n ≡ m

propagateAnd : forall {n m : ℕ} {P : ℕ -> Set} -> (n ≡ m × P n) -> P m
propagateAnd (zeron , second) rewrite zeron = second

thm :
 -- n comes from the signature
 -- n' comes from the recursive application in side
 forall (n : ℕ) -> Σ ℕ (\n' ->
   -- pre conditions
   (n ≥ 0) -> (n' ≥ 0 ×
    (forall (n0 n4 : ℕ) ->
      ((n4 + 1 ≡ n + 1) ×
        ¬ ((n0 ≡ 0) × ((n0 + 1) ≡ (n + 1))))
         -> (n4 ≡ n' + 1))))
thm n = 1 , λ pre → z≤n , λ n0 n4 pres →
  let (pre1 , pre2) = pres

      pre1' = inj+1 {n4} {n} pre1
      -- cong (\q -> ¬ q) (propagateAnd {n0} {0} {\n0 -> n0 + 1 ≡ n + 1}
  in {!!}
