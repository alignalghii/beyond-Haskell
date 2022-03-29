module Eq where

infix 4 _≡_
data _≡_ {A : Set} : A → A → Set where
    refl : ∀ {a : A} → a ≡ a

≡-symmetry : ∀ {A : Set} {a₁ a₂ : A} → a₁ ≡ a₂ → a₂ ≡ a₁
≡-symmetry refl = refl

≡-transitivity : ∀ {A : Set} {a₁ a₂ a₃ : A} → a₁ ≡ a₂ → a₂ ≡ a₃ → a₁ ≡ a₃
≡-transitivity refl refl = refl

leibniz : ∀ {A B : Set} (f : A → B) {a₁ a₂ : A} → a₁ ≡ a₂ → f a₁ ≡ f a₂
leibniz _ refl = refl
