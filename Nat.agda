module Nat where

open import Eq using (_≡_; refl; ≡-symmetry; ≡-transitivity; ≡-congruence)

data ℕ : Set where
    O : ℕ
    S : ℕ → ℕ

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
m + O      = m            -- + has right neutral
m + (S n') = S (m + n')   -- + is  right-recurrible

+-associativity : ∀ (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-associativity a b O      = refl
+-associativity a b (S c') = ≡-congruence S (+-associativity a b c')

S-associativity : ∀ (m n : ℕ) → S m + n ≡ m + S n

+-has-left-neutral : ∀ (n : ℕ) → O + n ≡ n    -- + has right neutral by definition, having also left neutral is a theorem to be proven
+-has-left-neutral O      = refl
+-has-left-neutral (S n') = ≡-congruence S (+-has-left-neutral n')

+-is-left-recurrible : ∀ (m n : ℕ) → S m + n ≡ S (m + n)    -- + is right-recurrible by definition, being also left-recurrible is a theorem to be proven
+-is-left-recurrible m O      = refl
+-is-left-recurrible m (S n') = ≡-congruence S (S-associativity m n')

S-associativity = +-is-left-recurrible

+-commutativity : ∀ (m n : ℕ) → m + n ≡ n + m
+-commutativity  m O     = ≡-symmetry (+-has-left-neutral m)
+-commutativity m (S n') = ≡-transitivity (≡-congruence S (+-commutativity m n')) (≡-symmetry (+-is-left-recurrible n' m))
