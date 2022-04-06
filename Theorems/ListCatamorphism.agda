module Theorems.ListCatamorphism where

open import Concepts.List using (List; _∷_; []; foldr)
open import Concepts.List using (List; _∷_; []; foldr)
open import Connectives.Eq using (_≡_; refl; ≡-congruence)
open import Connectives.Combinators using (_∘_)


catamorphism-identity : ∀ {A : Set} (as : List A) → foldr _∷_ [] as ≡ as
catamorphism-identity []       = refl
catamorphism-identity (a ∷ as) = ≡-congruence (_∷_ a) (catamorphism-identity as)

-----------------
-- Dark zone: ---
-----------------

-- catamorphism-identity = foldr (≡-congruence ∘ _∷_) refl -- wrong: metavar instatiation problems at the ∘-subterm
                                                           -- but works with dependent-type variants of foldr and ∘, see below:

_∘'_ : ∀ {A B : Set} {Predicate : B → Set} (f : ∀ (b : B) → Predicate b) (g : A → B) (a : A) → Predicate (g a)
(f ∘' g) a = f (g a)

foldr' : ∀ {M : Set} {Rel : List M → List M → Set} → (∀ (m : M) {ms₁ ms₂ : List M} → Rel ms₁ ms₂ → Rel (m ∷ ms₁) (m ∷ ms₂)) → Rel [] [] → ∀ (ms : List M) → Rel (foldr _∷_ [] ms) ms
foldr' consₘ₊ⁿ nilⁿ []       = nilⁿ
foldr' consₘ₊ⁿ nilⁿ (m ∷ ms) = consₘ₊ⁿ m (foldr' consₘ₊ⁿ nilⁿ ms)

catamorphism-identity' : ∀ {A : Set} (as : List A) → foldr _∷_ [] as ≡ as
catamorphism-identity' = foldr' (≡-congruence ∘' _∷_) refl


---------------------------
-- An even darker zone: ---
---------------------------


-- The typing of `foldr'` should be nicer, but I do not know yet how

-- These typings below do compile standalone, but do not compile together with the above definition of `catamorphism-identity`
--
-- ∀ {A : Set} (t : List A → List A) → (∀ (a : A) {as₂ : List A} → t as₂ ≡ as₂ → t (a ∷ as₂) ≡ a ∷ as₂) → t [] ≡ [] → ∀ (as : List A) → t as ≡ as
-- ∀ {A : Set} {Rel : List A → List A → Set} → (∀ (a : A) {as₁ as₂ : List A} → Rel as₁ as₂ → Rel (a ∷ as₁) (a ∷ as₂)) → Rel [] [] → ∀ (as : List A) → Rel (foldr _∷_ [] as) as
-- ∀ {A : Set} {t : List A → List A} → (∀ (a : A) {as₁ : List A} → t as₁ ≡ as₁ → t (a ∷ as₁) ≡ a ∷ as₁) → t [] ≡ [] → ∀ (as : List A) → t as ≡ as
-- ∀ {A : Set} → (∀ (a : A) {as : List A} → foldr _∷_ [] as ≡ as → foldr _∷_ [] (a ∷ as) ≡ a ∷ as) → foldr _∷_ [] [] ≡ [] → ∀ (as : List A) → foldr _∷_ [] as ≡ as
-- ∀ {A : Set} {Pr : List A → Set} (f : ∀ (a : A) {as : List A} → Pr as → Pr (a ∷ as)) → Pr [] → ∀ (as : List A) → Pr as

-- These typings below probably fail to compile even when compiled standalone (must be checked, I haven't checked all of them standalone):

-- ∀ {A : Set} {t : List A → List A} {Rel : List A → List A → Set} → (∀ (a : A) {as₁ : List A} → Rel (t as₁) as₁ → Rel (t (a ∷ as₁)) (a ∷ -- t as₁)) → Rel (t []) [] → ∀ (as : List A) → Rel (t as) as
-- ∀ {A : Set} {Pr : List A → Set} (∀ (a : A) {as as' : List A} → Pr as → Pr as') → Pr [] → ∀ (as : List A) → Pr as -- 90: expected sequence of possibly hidden bound identifiers
-- ∀ {A : Set} {Pr : List A → Set} (∀ (a : A) {as as' : List A} → Pr as → Pr as') → Pr [] → ∀ (as : List A) → Pr as
-- ∀ {A : Set} {Pr : List A → List A → Set} (f : ∀ (a : A) {as₁ as₂ : List A} → Pr as₁ as₂ → Pr (a ∷ as₁) (a ∷ as₂)) → Pr [] [] → ∀ (as : List A) → Pr as
-- ∀ {A : Set} {Pr : List A → List A → Set} (∀ (a : A) {as₁ as₂ : List A} → Pr as₁ as₂ → Pr (a ∷ as₁) (a ∷ as₂)) → Pr [] [] → ∀ (as : List A) → Pr as
-- ∀ {l1} {A : Set l1} {Pr : List A → Set l1} (f : ∀ (a : A) {as1 as1' : List A} → Pr as1 → Pr as1') → Pr [] → ∀ (as : List A) → Pr as
