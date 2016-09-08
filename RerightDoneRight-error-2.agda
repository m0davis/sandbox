open import Prelude

postulate
  𝐴 : Set

private
  _≢_ : ∀ {a} {A : Set a} → A → A → Set a
  A ≢ B = ¬ A ≡ B

data 𝕃 {𝑨} (𝐴 : Set 𝑨) : Set 𝑨
data _∉_ {𝑨} {𝐴 : Set 𝑨} (x : 𝐴) : 𝕃 𝐴 → Set 𝑨

data 𝕃 {𝑨} (𝐴 : Set 𝑨) where
  ∅ : 𝕃 𝐴
  ∷ : {x₀ : 𝐴} → {x₁s : 𝕃 𝐴} → x₀ ∉ x₁s → 𝕃 𝐴

data _∉_ {𝑨} {𝐴 : Set 𝑨} (𝔞 : 𝐴) where
  ∉∅ : 𝔞 ∉ ∅
  ∉∷ : ∀ {x₀} → 𝔞 ≢ x₀ → ∀ {x₁s} → 𝔞 ∉ x₁s → (x₀∉x₁s : x₀ ∉ x₁s) → 𝔞 ∉ (∷ x₀∉x₁s)

data _∈_ {𝑨} {𝐴 : Set 𝑨} (𝔞 : 𝐴) : 𝕃 𝐴 → Set 𝑨 where
  here : ∀ {x₀s} (𝔞∉x₀s : 𝔞 ∉ x₀s) → 𝔞 ∈ ∷ 𝔞∉x₀s
  there : ∀ {x₁s} → (𝔞∈x₁s : 𝔞 ∈ x₁s) → ∀ {x₀} → (x₀∉x₁s : x₀ ∉ x₁s)  → 𝔞 ∈ ∷ x₀∉x₁s

data ∈' (𝑨 : Level) (𝐴 : Set 𝑨) (𝔞 : 𝐴) : 𝕃 𝐴 → Set 𝑨 where
  here : ∀ {x₀s} (𝔞∉x₀s : 𝔞 ∉ x₀s) → ∈' 𝑨 𝐴 𝔞 (∷ 𝔞∉x₀s)
  there : ∀ {x₁s} → (𝔞∈x₁s : ∈' 𝑨 𝐴 𝔞 x₁s) → ∀ {x₀} → (x₀∉x₁s : x₀ ∉ x₁s)  → ∈' 𝑨 𝐴 𝔞 (∷ x₀∉x₁s)

open import Tactic.Reflection.Reright

¬∈→∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {𝔞} {xs : 𝕃 𝐴} → (∈' 𝑨 𝐴 𝔞 xs → ⊥) → 𝔞 ∉ xs
¬∈→∉ {𝔞 = 𝔞} {xs = ∅} ¬𝔞∈xs = ∉∅
¬∈→∉ {𝔞 = 𝔞} {xs = ∷ {x₀} {x₁s = ∅} x₀∉∅} ¬𝔞∈xs = ∉∷ (λ 𝔞≡x₀ → ⊥-elim (¬𝔞∈xs (reright 𝔞≡x₀ {!!}))) {!!} x₀∉∅ where -- error defining helper function
  open import Agda.Builtin.Reflection
¬∈→∉ {𝔞 = 𝔞} {xs = ∷ {x₀} {x₁s = ∷ {x₁} {x₂s} x₁∉x₂s} x₀∉x₁∉x₂s} ¬𝔞∈xs = {!!}
