module Connectives.Exists where

data Exists {A : Set} (predicate : A → Set) : Set where
    witness : ∀ (a : A) (proof : predicate a) → Exists predicate

Sum : ∀ (A : Set) → (A → Set) → Set
Sum A predicate = Exists {A} predicate
