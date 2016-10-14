--{-# OPTIONS -v profile:10 #-}
open import Agda.Builtin.Reflection
open import Postlude
module Map-GoalMatchHaveBug {𝑲} {K : Set 𝑲}     {{isDecEquivalence/K : Eq K}}
           {𝑽} (V : K → Set 𝑽) {{isDecEquivalence/V : (k : K) → Eq (V k)}}
           (let 𝑲𝑽 = 𝑲 ⊔ₗ 𝑽 ; 𝑲𝑽₁ = sucₗ 𝑲𝑽)
           (Carrier : ℕ → Set 𝑲𝑽)
       where

open import Tactic.Reflection.Reright

record Map : Set 𝑲𝑽₁ where
  field
    _∈_ : ∀ {s} → K → Carrier s → Set 𝑲𝑽

  _∉_ : ∀ {s} → K → Carrier s → Set 𝑲𝑽
  _∉_ k m = ¬ k ∈ m

  field
    ∅-is-empty : ∀ {𝑘} {∅ : Carrier 0} → 𝑘 ∉ ∅
    get : ∀ {k : K} {s} {m : Carrier s} → k ∈ m → V k
    get-is-unique : ∀ {k : K} {s} {m : Carrier s} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get k∈m¹ ≡ get k∈m²

  infixl 40 _⊆_
  _⊆_ : ∀ {s₀ s₁} → Carrier s₀ → Carrier s₁ → Set 𝑲𝑽
  _⊆_ m₀ m₁ = ∀ {𝑘} → (𝑘∈m₀ : 𝑘 ∈ m₀) → ∃ λ 𝑘∈m₁ → get 𝑘∈m₀ ≡ get {m = m₁} 𝑘∈m₁

  _⊆ᵉ_ : ∀ {s₀ s₁} → Carrier s₀ → Carrier s₁ → Set 𝑲𝑽
  _⊆ᵉ_ m₀ m₁ = (𝑘 : K) → (𝑘∈m₀ : 𝑘 ∈ m₀) → ∃ λ 𝑘∈m₁ → get 𝑘∈m₀ ≡ get {m = m₁} 𝑘∈m₁

  toE : ∀ {s₀ s₁} → {m₀ : Carrier s₀} → {m₁ : Carrier s₁} → (m₀ ⊆ m₁) → m₀ ⊆ᵉ m₁
  toE x 𝑘 𝑘∈m₀ = x {𝑘} 𝑘∈m₀

  ∅⊆⋆ : ∀ {∅ : Carrier 0} {s/⋆} {⋆ : Carrier s/⋆} → ∅ ⊆ ⋆
  ∅⊆⋆ {∅} = λ {𝑘∈⋆ → contradiction 𝑘∈⋆ (∅-is-empty {∅ = ∅})}

  postulate
    P : ∀ {a} (A : Set a) → Set a
    p : ∀ {a} {A : Set a} → (x : A) → P A

  union : ∀ {s/y} (x : Carrier 0) (y : Carrier s/y) → P (x ⊆ᵉ y)
  union x y = p $
    --(λ {k} → ∅⊆⋆)
    toE ∅⊆⋆

  postulate
    bar : ∀ {k : K} → Set
--  bar {k} = ℕ

  foo : P (∀ {k : K} → Set)
  foo = p {!bar!}
