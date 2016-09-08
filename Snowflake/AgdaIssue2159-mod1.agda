module Snowflake.AgdaIssue2159-mod1 where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data AB : Set where
  A B : AB

bar : AB → AB
bar A = A
bar B = A

foo : Nat → AB → AB
foo 0 t = bar t
foo (suc n) t = foo n (bar t) -- NB tail-recursive

test : foo 100000000 A ≡ A
test = refl -- memory blows up here
