module Connectives.Combinators where

const : {A B : Set} → A → B → A
const a _ = a

infixr 9 _∘_
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) a = f (g a)
