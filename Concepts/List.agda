module Concepts.List where


data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A

infixr 5 _∷_


foldr : ∀ {M N : Set} → (M → N → N) → N → List M → N
foldr consₘ₊ⁿ nilⁿ []       = nilⁿ
foldr consₘ₊ⁿ nilⁿ (m ∷ ms) = consₘ₊ⁿ m (foldr consₘ₊ⁿ nilⁿ ms)
