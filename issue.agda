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

-- ∀ n . ∃ n' .
--     (n ≥ 0) -> (n' ≥ 0 ∧
--                    ∀ n0 . ∀ n4 . ((n4 + 1 = n + 1) ∧ ¬ (n0 ≡ 0 ∧ n0 + 1 = n + 1))
--                      -> n4 = n' + 1
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

inv' : ¬ (forall (n : ℤ) -> (n ≥ ⟦ 0 ⟧) -> Σ ℤ (\n' ->
   -- pre conditions
    (n' ≥ ⟦ 0 ⟧ ×
    (forall (n0 n4 : ℤ) ->
      ((n4 + ⟦ 1 ⟧ ≡ n + ⟦ 1 ⟧) ×
        ¬ ((n0 ≡ ⟦ 0 ⟧) × ((n0 + ⟦ 1 ⟧) ≡ (n + ⟦ 1 ⟧))))
         -> (n4 ≡ n' + ⟦ 1 ⟧)))))
inv' x =
 let (n' , (q , q')) = x ⟦ 0 ⟧ (+≤+ z≤n)
     w = q' ⟦ 1 ⟧ ⟦ 0 ⟧
     w' = w (refl , λ x₁ → neq (proj₁ x₁))
 in lemma {n'} q w'



alt : ¬ (forall (n : ℤ) -> (n ≥ ⟦ 0 ⟧) ->
       Σ ℤ (\n14 -> (n14 ≥ ⟦ 0 ⟧) ×
         (forall (n0 : ℤ) -> (n0 ≥ ⟦ 0 ⟧) ->
            ((n0 + ⟦ 1 ⟧) ≡ (n + ⟦ 1 ⟧)) -> (n0 ≡ (n14 + ⟦ 1 ⟧)))))
alt x = {!!}

-- lem :

alt' : (forall (n : ℤ) -> (n ≥ ⟦ 0 ⟧) ->
         (forall (n0 : ℤ) -> (n0 ≥ ⟦ 0 ⟧) ->
            ((n0 + ⟦ 1 ⟧) ≡ (n + ⟦ 1 ⟧)) ->
              (Σ ℤ (\n14 -> (n14 ≥ ⟦ 0 ⟧) × (n0 ≡ (n14 + ⟦ 1 ⟧))))))
alt' n pn n0 pn0 p = {!!} , ({!!} , {!!})

lemSuc : (n : ℕ) -> (ℕ.suc n) ≡ (n Data.Nat.+ 1)
lemSuc zero = refl
lemSuc (ℕ.suc n) rewrite lemSuc n = refl

lemSucImpl : forall {k : ℤ} ->
   ¬ (k ≡ ⟦ 0 ⟧) -> (k ≥ ⟦ 0 ⟧) -> Σ ℤ (\k' -> k ≡ k' + ⟦ 1 ⟧)
lemSucImpl {+_ zero} p _ = -[1+ zero ] , refl
lemSucImpl {+_ (ℕ.suc n)} p _ rewrite lemSuc n = +_ n , refl
lemSucImpl { -[1+_] n} p1 ()

congSuc : forall {n m : ℕ} -> ℕ.suc n ≡ ℕ.suc m -> n ≡ m
congSuc {n} {.n} refl = refl

congPlusNat : forall {n m : ℕ} -> n Data.Nat.+ 1 ≡ m Data.Nat.+ 1 -> n ≡ m
congPlusNat {n} {m} p rewrite sym (lemSuc n) | sym (lemSuc m) | congSuc {n} {m} p = refl

congPos : forall {n m : ℕ} -> +_ n ≡ +_ m -> n ≡ m
congPos {n} {.n} refl = refl

postulate
  congPlus : forall {n m : ℤ} -> n + ⟦ 1 ⟧ ≡ m + ⟦ 1 ⟧ -> n ≡ m

{- congPlus {+_ n} {+_ m} p rewrite congPlusNat {n} {m} (congPos p) = refl
congPlus {+_ n} { -[1+_] n₁} p = {!!}
congPlus { -[1+_] n} {+_ n₁} p = {!!}
congPlus { -[1+_] n} { -[1+_] n₁} p = {!!} -}

propEq : (n n0 : ℤ) -> n0 ≡ ⟦ 0 ⟧ × n0 + ⟦ 1 ⟧ ≡ n + ⟦ 1 ⟧ -> n ≡ ⟦ 0 ⟧
propEq n n0 (p1 , p2) rewrite congPlus {n0} {n} p2 = p1

postulate
  invPropEq : (n n0 : ℤ) -> n ≡ ⟦ 0 ⟧ -> n0 ≡ ⟦ 0 ⟧ × n0 + ⟦ 1 ⟧ ≡ n + ⟦ 1 ⟧

prec : {P Q : Set} -> ¬ Q -> (P -> Q) -> ¬ P
prec {P} {Q} x p = λ y → x (p y)

-- Push the existentials down to the branches
altNewIdea : forall (n : ℤ) ->
   -- pre conditions
   (n ≥ ⟦ 0 ⟧) ->
   -- branch binders
    (forall (n4 : ℤ) ->
      -- branch conditions
      (n4 ≥ ⟦ 0 ⟧ × ((n4 + ⟦ 1 ⟧ ≡ n + ⟦ 1 ⟧) ×
         (forall (n0 : ℤ) -> ¬ ((n0 ≡ ⟦ 0 ⟧) × ((n0 + ⟦ 1 ⟧) ≡ (n + ⟦ 1 ⟧))))))
        ->
        -- branch consequence
        (Σ ℤ (\n' -> (n' ≥ ⟦ 0 ⟧ × (n4 ≡ n' + ⟦ 1 ⟧)))))
altNewIdea n np n4 (prec0 , (prec1 , prec2)) = -- rewrite propEq n0 n {!!} =
 let -- y = cong (\p -> ¬ p) (propEq n0 n ?)
     y = prec2 n4
     (k' , prf) = lemSucImpl {n4} (λ z → prec2 n4 (z , prec1)) prec0
 in k' , {!!} , {!prf!}
