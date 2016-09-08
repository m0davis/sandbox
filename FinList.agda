module FinList where

open import Prelude.Nat

data FinList (A : Set) : (n : Nat) → Set where
  ∅ : FinList A 0
  _∷_ : A → ∀ {n : Nat} → FinList A n → FinList A (suc n)
