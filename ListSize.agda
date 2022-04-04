module ListSize where

open import List using (List; []; _∷_; foldr)
open import Nat using (ℕ; O; S)
open import Combinators using (const)
open import Eq using (_≡_; refl; ≡-congruence)
open import Exists using (Sum; Exists; witness)


length : ∀ {A : Set} → List A → ℕ
length = foldr (const S) O

-- Single-statement proof:

every-number-can-be-a-list-length-for-inhabitated-types : ∀ {A : Set} (a : A) (n : ℕ) → Exists {List A} (λ as → length as ≡ n)
every-number-can-be-a-list-length-for-inhabitated-types _ O     = witness [] refl
every-number-can-be-a-list-length-for-inhabitated-types a (S n) with every-number-can-be-a-list-length-for-inhabitated-types a n
...                                                                | witness as |as|≡n = witness (a ∷ as) (≡-congruence S |as|≡n)

-- Proof with a standalone witness-generating function and a lemma:

replicate : ∀ {A : Set} → ℕ → A → List A
replicate O     _ = []
replicate (S n) a = a ∷ replicate n a

replicate-length : ∀ {A : Set} (n : ℕ) (a : A) → length (replicate n a) ≡ n
replicate-length O     _ = refl
replicate-length (S n) a = ≡-congruence S (replicate-length n a)

every-number-can-be-a-list-length-for-inhabitated-types-2 : ∀ {A : Set} (a : A) (n : ℕ) → Exists {List A} (λ as → length as ≡ n)
every-number-can-be-a-list-length-for-inhabitated-types-2 a n = witness (replicate n a) (replicate-length n a)
