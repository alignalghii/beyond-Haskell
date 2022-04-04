module Theorems.ListSize where

open import MyData.List using (List; []; _∷_; foldr)
open import MyData.List using (List; []; _∷_; foldr)
open import MyData.Nat using (ℕ; O; S)
open import MyData.Nat using (ℕ; O; S)
open import Combinators using (const)
open import Eq using (_≡_; refl; ≡-congruence)
open import Exists using (Sum; Exists; witness)


length : ∀ {A : Set} → List A → ℕ
length = foldr (const S) O

-- A compact proof compressed in a single function:

every-number-can-be-a-list-length-for-inhabitated-types : ∀ {A : Set} (a : A) (n : ℕ) → Exists {List A} (λ as → length as ≡ n)
every-number-can-be-a-list-length-for-inhabitated-types _ O     = witness [] refl
every-number-can-be-a-list-length-for-inhabitated-types a (S n) with every-number-can-be-a-list-length-for-inhabitated-types a n
...                                                                | witness as |as|≡n = witness (a ∷ as) (≡-congruence S |as|≡n)

-- A less dense proof delegating subcalculations to an auxiliary witness-generating function and to a lemma:

replicate : ∀ {A : Set} → ℕ → A → List A
replicate O     _ = []
replicate (S n) a = a ∷ replicate n a

replicate-length-lemma : ∀ {A : Set} (n : ℕ) (a : A) → length (replicate n a) ≡ n
replicate-length-lemma O     _ = refl
replicate-length-lemma (S n) a = ≡-congruence S (replicate-length-lemma n a)

every-number-can-be-a-list-length-for-inhabitated-types-2 : ∀ {A : Set} (a : A) (n : ℕ) → Exists {List A} (λ as → length as ≡ n)
every-number-can-be-a-list-length-for-inhabitated-types-2 a n = witness (replicate n a) (replicate-length-lemma n a)
