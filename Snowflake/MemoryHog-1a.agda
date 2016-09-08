module Snowflake.MemoryHog-1a where

-- 𝕃 is a list of unique elements (each element distinct from every other)
-- 𝑳 is a regular List

open import Agda.Builtin.Strict

infixr 0 _$!_
_$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $! x = primForce x f

data [erased]-is-only-for-printing : Set where
  [erased] : [erased]-is-only-for-printing

data ⊥ : Set where

infix 3 ¬_
¬_ : ∀ {a} (A : Set a) → Set a
¬ A = A → ⊥

private postulate erasedBottom : ⊥

{-# DISPLAY erasedBottom = [erased] #-}

erase-⊥ : ⊥ → ⊥
erase-⊥ _ = erasedBottom

eraseNegation : ∀ {a} {A : Set a} → ¬ A → ¬ A
eraseNegation !a a = erase-⊥ (!a a)

open import Agda.Primitive
open import Agda.Builtin.Nat public
     using ( zero
           ; suc
           ; _-_
           ; _+_
           )
  renaming (Nat to ℕ)
open import Agda.Builtin.Equality public
     using (_≡_; refl)
open import Agda.Builtin.List public
     using ()
  renaming (List to 𝑳
           ;[] to ∅
           ; _∷_ to _∷ₗ_
           )

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P y → P x
subst P refl px = px

_≢_ : ∀ {a} {A : Set a} → A → A → Set a
A ≢ B = ¬ A ≡ B

data 𝕃 {𝑨} (𝐴 : Set 𝑨) : Set 𝑨
data _∉_ {𝑨} {𝐴 : Set 𝑨} (x : 𝐴) : 𝕃 𝐴 → Set 𝑨

data 𝕃 {𝑨} (𝐴 : Set 𝑨) where
  ∅ : 𝕃 𝐴
  ✓ : {x₀ : 𝐴} → {x₁s : 𝕃 𝐴} → x₀ ∉ x₁s → 𝕃 𝐴

data _∉_ {𝑨} {𝐴 : Set 𝑨} (𝔞 : 𝐴) where
  ∅ : 𝔞 ∉ ∅
  ● : ∀ {x₀} → 𝔞 ≢ x₀ → ∀ {x₁s} → 𝔞 ∉ x₁s → (x₀∉x₁s : x₀ ∉ x₁s) → 𝔞 ∉ ✓ x₀∉x₁s

pattern tail= x₁s = ✓ {x₁s = x₁s} _
pattern [_] x₀ = ✓ {x₀ = x₀} ∅
pattern _₀∷₁_∷⟦_⟧ x₀ x₁ x₂s = ✓ {x₀ = x₀} (● {x₁} _ {x₂s} _ _)

pattern _↶_↷_ x₀∉x₂s x₀≢x₁ x₁∉x₂s = ● x₀≢x₁ x₀∉x₂s x₁∉x₂s

𝕃→𝑳 : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → 𝑳 𝐴
𝕃→𝑳 ∅ = ∅
𝕃→𝑳 [ x ] = x ∷ₗ ∅
𝕃→𝑳 (x₀ ₀∷₁ x₁ ∷⟦ x₂s ⟧) = x₀ ∷ₗ x₁ ∷ₗ 𝕃→𝑳 x₂s

sym≢ : ∀ {𝑨} {𝐴 : Set 𝑨} {x y : 𝐴} → x ≢ y → y ≢ x
sym≢ x₁ x₂ = x₁ (sym x₂)

postulate
  T : Set
  ⋆a ⋆b : T
  a≢b : ⋆a ≢ ⋆b

b≢a = sym≢ a≢b
a∉b   = ∅ ↶ a≢b ↷ ∅
b∉a   = ∅ ↶ b≢a ↷ ∅

[ab] [ba] : 𝕃 T

[ab]   = ✓ $! a∉b
[ba]   = ✓ $! b∉a

-- swapTop "AB23456789" = "BA23456789"
swapTop : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → 𝕃 𝐴
swapTop ∅ = ∅
swapTop [ x₀ ] = (✓ {x₀ = x₀}) $! ∅
--swapTop (✓ (x₀∉x₂s ↶ x₀≢x₁ ↷ x₁∉x₂s)) = ✓ (x₁∉x₂s ↶ (sym≢ x₀≢x₁) ↷ x₀∉x₂s)
swapTop (✓ (x₀∉x₂s ↶ x₀≢x₁ ↷ x₁∉x₂s)) = ✓ $! (((● $! (eraseNegation $! (sym≢ $! x₀≢x₁))) $! x₁∉x₂s) $! x₀∉x₂s)

--swapTop-ex : 𝕃→𝑳 (swapTop [ab]) ≡ (⋆b ∷ₗ ⋆a ∷ₗ ∅)
--swapTop-ex = refl

{-# TERMINATING #-}
swapTopBy : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
swapTopBy 0 x = x
swapTopBy (suc n) x = (swapTopBy $! n) $! swapTop x

test : ((swapTopBy $! 10{-000000-}) $! [ab]) ≡ [ab]
test = {!refl!}
