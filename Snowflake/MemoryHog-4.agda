module Snowflake.MemoryHog-4 where

open import Agda.Builtin.Strict
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

infixr 0 _$!_
_$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $! x = primForce x f

id : {A : Set} → A → A
id x = x

postulate
  A : Set
  a b : A

data Pair : Set where
  pair : A → A → Pair

reverse : Pair → Pair
reverse (pair a b) = pair (id b) (id a)

reverseBy : Nat → Pair → Pair
reverseBy 0 x = x
reverseBy (suc n) x = reverseBy n $! (reverse x)

test-reverse₂ : reverseBy 2 (pair a b) ≡ pair a b
test-reverse₂ = refl

test-reverse! : reverseBy 1000000 (pair a b) ≡ pair a b
test-reverse! = refl
