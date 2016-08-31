module Snowflake.Simple where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data AB : Set where
  A B : AB

foo : Nat → AB → AB
foo 0 t = A
foo (suc n) t = foo n A -- NB tail-recursive

test : foo 10000000 A ≡ A
test = refl -- memory blows up here
