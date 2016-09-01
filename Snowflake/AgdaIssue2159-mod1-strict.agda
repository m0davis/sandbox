module Snowflake.AgdaIssue2159-mod1-strict where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Strict

data AB : Set where
  A B : AB

bar : AB → AB
bar A = A
bar B = A

infixr 0 _$!_
_$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $! x = primForce x f

foo : Nat → AB → AB
foo 0 t = bar t
foo (suc n) t = foo n $! bar t -- NB tail-recursive

test : foo 10000000 A ≡ A
test = primForceLemma 9999999 (λ n → foo n A) -- memory doesn't blow up here!
