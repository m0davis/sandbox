module Strictness.Pow1 where

open import Agda.Builtin.Strict
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- pow₁ n a = a 2ⁿ⁺¹
pow₁ : Nat → Nat → Nat
pow₁ zero    a = a
pow₁ (suc n) a = pow₁ n (a + a)

test-pow₁ : pow₁ 7 2 ≡ 256
test-pow₁ = refl

foo₁ : Nat → Nat → Nat
foo₁ zero    a = a
foo₁ (suc n) a = foo₁ n (a - a)

test-2s₁ : 2 ≡ 2
test-2s₁ = refl

test-2s₂ : 2 - 2 ≡ 0
test-2s₂ = refl

test-2s₃ : (2 - 2) - (2 - 2) ≡ 0
test-2s₃ = refl

test-2s₄ : ((2 - 2) - (2 - 2)) - ((2 - 2) - (2 - 2)) ≡ 0
test-2s₄ = refl

test-foo₁ : foo₁ 7{-22-} 2 ≡ 0
test-foo₁ = refl

infixr 0 _$!_
_$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $! x = primForce x f

-- pow₂ n a = a 2ⁿ⁺¹
pow₂ : Nat → Nat → Nat
pow₂ zero    a = a
pow₂ (suc n) a =  pow₂ n $! a + a

foo₂ : Nat → Nat → Nat
foo₂ zero    a = a
foo₂ (suc n) a =  foo₂ n $! a - a

test-foo₂ : foo₂ 22 2 ≡ 0
test-foo₂ = refl


foo₃ : Nat → Nat → Nat
foo₃ zero    a = a
foo₃ (suc n) a = let z = a - a in foo₃ n $! z

test-foo₃ : foo₃ 22 2 ≡ 0
test-foo₃ = refl
