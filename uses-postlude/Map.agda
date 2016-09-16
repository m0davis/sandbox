module Map where
  open import Postlude
  open import Tactic.Reflection.Reright

  module _ {𝑲 𝑽} (let 𝑲𝑽 = 𝑲 ⊔ₗ 𝑽 ; 𝑲𝑽₁ = sucₗ 𝑲𝑽) where
    record Map
             {K : Set 𝑲}
             (V : K → Set 𝑽)
             (Carrier : ℕ → Set 𝑲𝑽) (isDecEquivalence/K : Eq K) : Set 𝑲𝑽₁ where
      field
        _∈_ : ∀ {s} → K → Carrier s → Set 𝑲𝑽
        get : ∀ {k : K} {s} {m : Carrier s} → k ∈ m → V k

      infixl 40 _⊆_
      _⊆_ : ∀ {s₁ s₀} → Carrier s₁ → Carrier s₀ → Set 𝑲𝑽
      _⊆_ m₁ m₀ = ∀ {𝑘} → (𝑘∈m₁ : 𝑘 ∈ m₁) → ∃ λ (𝑘∈m₀ : 𝑘 ∈ m₀) → get 𝑘∈m₁ ≡ get 𝑘∈m₀

      field
        choose : ∀ {s} → (m : Carrier s) → Dec (∃ λ k → k ∈ m)

      union : ∀ {s/x} (x : Carrier s/x) → ∃ λ s/z → ∃ λ (z : Carrier s/z) → (x ⊆ z)
      union {0} x = {!!}
      union {suc s/x₋ₐ} x with choose x
      union {suc s/x₋ₐ} x | yes (a , a∈x) =
        {!!} ,
        {!!} ,
        (λ {𝑘} ∈x → case _≟_ {{isDecEquivalence/K}} 𝑘 a of
          (λ {
            (yes 𝑘≡a) → reright 𝑘≡a {!!}
          ; (no 𝑘≢a) → {!!}
          }))
      union {suc s/x₋ₐ} x | no ∉x = {!!}
