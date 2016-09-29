{-# OPTIONS --show-implicit #-}
module SnowflakeCev where
  open import Prelude
    using ( ⊥
          ; ¬_
          ; _≡_
          ; ⊤
          ; case_of_
          ; ⊥-elim
          ; refl
--          ; ∃
          ; _≤_
          ; id
          )

  open import Relation.Binary.PropositionalEquality using (subst)
  open import Tactic.Nat.Generic (quote _≤_) (quote id) (quote id)
  open import Agda.Builtin.Nat using (suc; _+_) renaming (Nat to ℕ)

  _≢_ : ∀ {a} {A : Set a} → A → A → Set a
  A ≢ B = ¬ (A ≡ B)

  data 𝕍 {𝑨} (𝐴 : Set 𝑨) : ℕ → Set 𝑨
  data _∉_ {𝑨} {𝐴 : Set 𝑨} (x : 𝐴) : ∀ {n} → 𝕍 𝐴 n → Set 𝑨

  data 𝕍 {𝑨} (𝐴 : Set 𝑨) where
    ε : 𝕍 𝐴 0
    φ : ∀ {x₀ n₁} {x₁s : 𝕍 𝐴 n₁} → x₀ ∉ x₁s → 𝕍 𝐴 (suc n₁)

  data _∉_ {𝑨} {𝐴 : Set 𝑨} (𝔞 : 𝐴) where
    ε : 𝔞 ∉ ε
    φ : ∀ {x₀ n} {x₁s : 𝕍 𝐴 n} → {x₀∉x₁s : x₀ ∉ x₁s} → 𝔞 ≢ x₀ → 𝔞 ∉ x₁s → 𝔞 ∉ (φ x₀∉x₁s)

  data _∈_ {𝑨} {𝐴 : Set 𝑨} (𝔞 : 𝐴) : ∀ {n} → 𝕍 𝐴 n → Set 𝑨 where
    here : ∀ {n₀} {x₀s : 𝕍 𝐴 n₀} (𝔞∉x₀s : 𝔞 ∉ x₀s) → 𝔞 ∈ φ 𝔞∉x₀s
    there : ∀ {x₀ n₁} {x₁s : 𝕍 𝐴 n₁} (x₀∉x₁s : x₀ ∉ x₁s) (𝔞∈x₁s : 𝔞 ∈ x₁s) → 𝔞 ∈ φ x₀∉x₁s

  data _[_]=_ {𝑨} {𝐴 : Set 𝑨} : ∀ {n} → 𝕍 𝐴 n → ℕ → 𝐴 → Set 𝑨 where
    here  : ∀ {𝔞 n} {xs : 𝕍 𝐴 n} (𝔞∉xs : 𝔞 ∉ xs) → φ 𝔞∉xs [ 0 ]= 𝔞
    there : ∀ {i 𝔞 x₀ n₁} {x₁s : 𝕍 𝐴 n₁} {x₀∉x₁s : x₀ ∉ x₁s} (x₁s[i]=𝔞 : x₁s [ i ]= 𝔞) → φ x₀∉x₁s [ suc i ]= 𝔞

  ∉→∈→⊥ : ∀ {𝑨} {𝐴 : Set 𝑨} {𝔞 n} {xs : 𝕍 𝐴 n} → 𝔞 ∉ xs → 𝔞 ∈ xs → ⊥
  ∉→∈→⊥ ε ()
  ∉→∈→⊥ (φ x₀≢x₀ _) (here _) = x₀≢x₀ refl
  ∉→∈→⊥ (φ 𝔞≢x₀ 𝔞∉x₁s) (there x₀∉x₁s 𝔞∈x₁s) = ∉→∈→⊥ 𝔞∉x₁s 𝔞∈x₁s

  head : ∀ {𝑨} {𝐴 : Set 𝑨} {n} → 𝕍 𝐴 (suc n) → 𝐴
  head (φ {x₀} _) = x₀

  tail : ∀ {𝑨} {𝐴 : Set 𝑨} {n} → 𝕍 𝐴 (suc n) → 𝕍 𝐴 n
  tail (φ {x₁s = x₁s} _) = x₁s

  last : ∀ {𝑨} {𝐴 : Set 𝑨} {n} → 𝕍 𝐴 (suc n) → 𝐴
  last (φ {x₀} {0} _) = x₀
  last (φ {x₁s = φ x₁∉x₂s} _) = last (φ x₁∉x₂s)

  data ⌜_∩_≡∅⌝ {𝑨} {𝐴 : Set 𝑨} : ∀ {m} → 𝕍 𝐴 m → ∀ {n} → 𝕍 𝐴 n → Set 𝑨 where
    ε : ∀ {n₀} {y₀s : 𝕍 𝐴 n₀} → ⌜ ε ∩ y₀s ≡∅⌝
    φ : ∀ {m₀} {x₀s : 𝕍 𝐴 (suc m₀)} {n₀} {y₀s : 𝕍 𝐴 n₀} → (x₀∉y₀s : head x₀s ∉ y₀s) →  ⌜ tail x₀s ∩ φ x₀∉y₀s ≡∅⌝ → ⌜ x₀s ∩ y₀s ≡∅⌝

  ∪ : ∀ {𝑨} {𝐴 : Set 𝑨} {m₀} {x₀s : 𝕍 𝐴 m₀} {n₀} {y₀s : 𝕍 𝐴 n₀} → ⌜ x₀s ∩ y₀s ≡∅⌝ → 𝕍 𝐴 (m₀ + n₀)
  ∪ (ε {y₀s = y₀s}) = y₀s
  ∪ (φ {m₀} {x₀s = x₀s} {n₀} {y₀s = y₀s} x₀∉y₀s x₁s∩x₀y₀s≡∅) = subst (𝕍 _) auto (∪ x₁s∩x₀y₀s≡∅)
