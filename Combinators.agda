module Combinators where

infixr 9 _∘_
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) a = f (g a)
