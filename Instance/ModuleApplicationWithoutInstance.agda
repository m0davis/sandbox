open import Agda.Builtin.Nat using (Nat)

-- module application, no instance
import Agda.Builtin.FromNat

--open import Prelude.Nat -- need this (an instance of Number Nat) to avoid error

zero : Nat
zero = 0 -- error, no instance
{-
No instance of type Agda.Builtin.FromNat.Number Nat was found in
scope.
when checking that 0 is a valid argument to a function of type
{a : .Agda.Primitive.Level} {A : Set a}
{{r : Agda.Builtin.FromNat.Number A}} (n : Nat)
{{_ : Agda.Builtin.FromNat.Number.Constraint r n}} →
A
-}
