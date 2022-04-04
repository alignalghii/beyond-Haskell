module Theorems.ListCatamorphism where

open import MyData.List using (List; _∷_; []; foldr)
open import MyData.List using (List; _∷_; []; foldr)
open import Connectives.Eq using (_≡_; refl; ≡-congruence)
open import Connectives.Combinators using (_∘_)


catamorphism-identity : ∀ {A : Set} (as : List A) → foldr _∷_ [] as ≡ as
catamorphism-identity []       = refl
catamorphism-identity (a ∷ as) = ≡-congruence (_∷_ a) (catamorphism-identity as)
-- catamorphism-identity = foldr (≡-congruence ∘ _∷_) refl -- metavar instatiation problems at the ∘-subterm
