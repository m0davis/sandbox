open import Prelude

module _ (A : Set) (P : A → Set) where

  data _isNotHeadOf_ (𝔞 : 𝐴) : List 𝐴 → Set where
    ∉∅ : 𝔞 isNotHeadOf []
    ∉∷ : ∀ {x₀} → ¬ 𝔞 ≡ x₀ → ∀ {x₁s} → 𝔞 isNotHeadOf (x₀ ∷ x₁s)

  test₁ : ∀ {𝔞 : 𝐴} → (xs : List 𝐴) → E 𝔞 → 𝔞 isNotHeadOf xs
  test₁ [] _ = ∉∅
  test₁ (_ ∷ _) _ = ∉∷ (λ 𝔞≡x₀ → reright 𝔞≡x₀ {!!})
