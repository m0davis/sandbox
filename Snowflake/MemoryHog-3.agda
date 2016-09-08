module Snowflake.MemoryHog-3 where

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

id : {A : Set} → A → A
id x = x

data Nat' : Set where
  zero : Nat'
  suc : Nat' → Nat'

foo : Nat' → Nat'
foo zero = zero
foo (suc b) = suc $! (id b)

fooBy : Nat → Nat' → Nat'
fooBy zero x = x
fooBy (suc n) x = fooBy n $! foo x
--fooBy (suc n) x = fooBy n (foo x)

test : fooBy 10{-000000-} (suc zero) ≡ suc zero
test = {!refl!}
{-
-- with $! in fooBy
Goal: ((λ x →
          (λ x₁ →
             (λ x₂ →
                (λ x₃ →
                   (λ x₄ →
                      (λ x₅ →
                         (λ x₆ →
                            (λ x₇ → (λ x₈ → (λ x₉ → x₉) $! foo x₈) $! foo x₇) $! foo x₆)
                         $! foo x₅)
                      $! foo x₄)
                   $! foo x₃)
                $! foo x₂)
             $! foo x₁)
          $! foo x)
       $! suc $! id zero)
      ≡ suc zero
-- without $!
Goal: (suc $! id zero) ≡ suc zero

Goal: fooBy 10 (suc zero) ≡ suc zero
Goal: suc zero ≡ suc zero

-}
