module PatternLambda where
  open import Prelude
  open import Tactic.Reflection

  data 𝑫 : Set where
    D : Nat → 𝑫

  unD : 𝑫 → 𝑫 → Nat
  unD = λ { (D n) (D n1) → n }

  f : Set
  f = {!evalT (quoteTC unD)!}
