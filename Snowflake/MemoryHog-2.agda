module Snowflake.MemoryHog-2 where

open import Agda.Builtin.Strict

infixr 0 _$!_
_$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $! x = primForce x f

open import Agda.Builtin.Nat
     using ( zero
           ; suc
           ; Nat
           )
open import Agda.Builtin.Equality
     using (_≡_; refl)

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

data D : Set where
  empty : D
  double : (a : D) → (b : D) → a ≡ b → D

swapL : D → D
swapL empty = empty
swapL (double a b a≡b) = double b a (sym a≡b)

swapLBy : Nat → D → D
swapLBy zero x = x
swapLBy (suc n) x = swapLBy n $! swapL x

exampleD : D
exampleD = double empty empty refl

test : swapLBy 10000000 exampleD ≡ exampleD
test = {!refl!}
