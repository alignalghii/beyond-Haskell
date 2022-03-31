module NatModulo where

open import Eq using (_≡_; refl; ≡-transitivity; ≡-congruence)
open import Exists using (Exists; witness)

open import Nat using (ℕ; O; S; _+_; +-is-left-recurrible)
open import NatNotation using (№0; №2; №4)


data Even : ℕ → Set where
    even₀  : Even O
    even₊₂ : ∀ {n : ℕ} → Even n → Even (S (S n))


-- Examples for existential `minitheorems':

0-is-even : Exists Even
0-is-even = witness №0 even₀

2-is-even : Exists Even
2-is-even = witness №2 (even₊₂ even₀)

4-is-halvable : Exists (λ n → n + n ≡ №4)
4-is-halvable = witness №2 refl


-- A simple universal theorem for existentials:

every-even-is-halvable : ∀ {n : ℕ} → Even n → Exists (λ ½n → ½n + ½n ≡ n)
every-even-is-halvable even₀              = witness O refl
every-even-is-halvable (even₊₂ evennessₙ) with every-even-is-halvable evennessₙ
...                                          | witness ½n ½n+½n≡n = witness (S ½n)
                                                                            (≡-transitivity (+-is-left-recurrible ½n (S ½n))
                                                                                            (≡-congruence S (≡-congruence S ½n+½n≡n))
                                                                            )
