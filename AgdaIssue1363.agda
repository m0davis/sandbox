module AgdaIssue1363 where
  open import Prelude
  open import Tactic.Reflection

  postulate
    F : Set → Set

  module M₀ where
    macro
      go-tactic₀ : Tactic
      go-tactic₀ hole = unify hole (def₀ (quote F))

    test₀ : Set
    test₀ = go-tactic₀ Nat

  module M₁ (A : Set) where
    macro
      go-tactic₁ : Tactic
      go-tactic₁ hole = unify hole (def₀ (quote F))

    test-inside-M₁ : Set
    test-inside-M₁ = {!go-tactic₁ Nat!}

  test-outside-M₁ : Set
  test-outside-M₁ = M₁.go-tactic₁ Nat Nat

  open M₁

  test-in-open-M₁ : Set
  test-in-open-M₁ = go-tactic₁ Nat Nat
