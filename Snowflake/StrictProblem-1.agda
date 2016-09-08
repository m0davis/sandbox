module Snowflake.StrictProblem-1 where

open import Agda.Builtin.Strict

infixr 0 _$!_
_$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $! x = primForce x f

data ⊥ : Set where

infix 3 ¬_
¬_ : ∀ {a} (A : Set a) → Set a
¬ A = A → ⊥

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

_≢_ : ∀ {a} {A : Set a} → A → A → Set a
A ≢ B = ¬ A ≡ B

module 𝕃-List where
  data 𝕃 (𝐴 : Set) : Set
  data _∉_ {𝐴 : Set} (x : 𝐴) : 𝕃 𝐴 → Set

  data 𝕃 (𝐴 : Set) where
    ∅ : 𝕃 𝐴
    ✓ : {x₀ : 𝐴} → {x₁s : 𝕃 𝐴} → x₀ ∉ x₁s → 𝕃 𝐴

  data _∉_ {𝐴 : Set} (𝔞 : 𝐴) where
    ∅ : 𝔞 ∉ ∅
    ● : ∀ {x₀} → 𝔞 ≢ x₀ → ∀ {x₁s} → 𝔞 ∉ x₁s → (x₀∉x₁s : x₀ ∉ x₁s) → 𝔞 ∉ ✓ x₀∉x₁s

  data ∅⊂ {𝐴 : Set} : 𝕃 𝐴 → Set where
    ✓ : ∀ {x₀ x₁s} → (x₀∉x₁s : x₀ ∉ x₁s) → ∅⊂ (✓ x₀∉x₁s)

  data _[_]=_ {𝐴 : Set} : 𝕃 𝐴 → ℕ → 𝐴 → Set where
    here  : ∀ {𝔞 xs} (𝔞∉xs : 𝔞 ∉ xs) → ✓ 𝔞∉xs [ 0 ]= 𝔞
    there : ∀ {x₀ x₁s} (x₀∉x₁s : x₀ ∉ x₁s) {i 𝔞} (x₁s[i]=𝔞 : x₁s [ i ]= 𝔞) → ✓ x₀∉x₁s [ suc i ]= 𝔞

  {-
  lastIndex : ∀ {𝐴 : Set} {L : 𝕃 𝐴} (∅⊂L : ∅⊂ L) → ℕ
  lastIndex [ _ ] = 0
  lastIndex (✓ (_ ↶ _ ↷ x₀∉x₁s)) = suc (lastIndex (✓ x₀∉x₁s))

  last : ∀ {𝐴 : Set} {L} → ∅⊂ L → 𝐴
  last [ x₀ ] = x₀
  last (tail= (✓ x₁∉x₂s)) = last $! (∅⊂_.✓ x₁∉x₂s)

  _[lastIndex]=last : ∀ {𝐴 : Set} {L : 𝕃 𝐴} → (∅⊂L : ∅⊂ L) → L [ lastIndex ∅⊂L ]= last ∅⊂L
  [ _ ] [lastIndex]=last = here ∅
  (✓ (x₀∉x₁s₁ ↶ x ↷ x₀∉x₁s)) [lastIndex]=last = there (x₀∉x₁s₁ ↶ x ↷ x₀∉x₁s) (✓ x₀∉x₁s [lastIndex]=last)
  -}

  lastIndex : ∀ {𝐴 : Set} {L : 𝕃 𝐴} (∅⊂L : ∅⊂ L) → ℕ
  lastIndex (✓ ∅) = 0
  lastIndex (✓ (● _ _ x₀∉x₁s)) = ℕ.suc (lastIndex (✓ x₀∉x₁s))

  last : ∀ {𝐴 : Set} {L} → ∅⊂ L → 𝐴
  last (✓ {x₀ = x₀} ∅) = x₀
  last (✓ {x₁s = (✓ x₁∉x₂s)} _) = last (∅⊂.✓ x₁∉x₂s)

  prf : ∀ {𝐴 : Set} {L : 𝕃 𝐴} → (∅⊂L : ∅⊂ L) → L [ lastIndex ∅⊂L ]= last ∅⊂L
  prf (✓ ∅) = here ∅
  prf (✓ (● x x₀∉x₁s₁ x₀∉x₁s)) = there (● x x₀∉x₁s₁ x₀∉x₁s) (prf (✓ x₀∉x₁s))

module 𝑳-List where
  data ∅⊂ {𝐴 : Set} : 𝑳 𝐴 → Set where
    ✓ : (x₀ : 𝐴) (x₁s : 𝑳 𝐴)  → ∅⊂ (x₀ ∷ₗ x₁s)

  data _[_]=_ {𝐴 : Set} : 𝑳 𝐴 → ℕ → 𝐴 → Set where
    here  : ∀ {𝔞 xs} → (𝔞 ∷ₗ xs) [ 0 ]= 𝔞
    there : ∀ {x₀ x₁s} {i 𝔞} (x₁s[i]=𝔞 : x₁s [ i ]= 𝔞) → (x₀ ∷ₗ x₁s) [ suc i ]= 𝔞

  lastIndex : ∀ {𝐴 : Set} {L : 𝑳 𝐴} (∅⊂L : ∅⊂ L) → ℕ
  lastIndex (✓ _ ∅) = 0
  lastIndex (✓ x₀ (x₁ ∷ₗ x₂s)) = ℕ.suc (lastIndex (✓ x₁ x₂s))

  last : ∀ {𝐴 : Set} {L} → ∅⊂ L → 𝐴
  last (✓ x₀ ∅) = x₀
  last (✓ x₀ (x₁ ∷ₗ x₂s)) = last (∅⊂.✓ x₁ x₂s)

  prf : ∀ {𝐴 : Set} {L : 𝑳 𝐴} → (∅⊂L : ∅⊂ L) → L [ lastIndex ∅⊂L ]= last ∅⊂L
  prf (✓ x₀ ∅) = here
  prf (✓ x₀ (x₁ ∷ₗ x₂s)) = there {!!} -- (● x x₀∉x₁s₁ x₀∉x₁s) (prf (✓ x₀∉x₁s))

module 𝑳-List₂ where
  data ∅⊂₂ : ℕ → Set where
    ✓ : (n : ℕ) → ∅⊂₂ n

  data [_]₂ : ℕ → Set where
    here  : [ 0 ]₂
    there : ∀ {i} → [ suc i ]₂

  lastIndex₂ : ∀ {n : ℕ} → (∅⊂L : ∅⊂₂ n) → ℕ
  lastIndex₂ (✓ 0) = 0
  lastIndex₂ (✓ (suc n)) = ℕ.suc (lastIndex₂ (✓ n))

  prf₂ : ∀ {n : ℕ} → (∅⊂L : ∅⊂₂ n) → [ lastIndex₂ ∅⊂L ]₂
  prf₂ (✓ 0) = here
  prf₂ (✓ (suc n)) = there

module 𝑳-List₃ where
  data ∅⊂₂ : ℕ → Set where
    ✓ : (n : ℕ) → ∅⊂₂ n

  data [_]₂ : ℕ → Set where
    here  : [ 0 ]₂
    there : ∀ {i} → [ suc i ]₂

  lastIndex₂ : ∀ {n : ℕ} → (∅⊂L : ∅⊂₂ n) → ℕ
  lastIndex₂ (✓ 0) = 0
  lastIndex₂ (✓ (suc n)) = ℕ.suc (lastIndex₂ (✓ n))

  prf₂ : ∀ {n : ℕ} → (∅⊂L : ∅⊂₂ n) → [ lastIndex₂ ∅⊂L ]₂
  prf₂ (✓ 0) = here
  prf₂ (✓ (suc n)) = there
