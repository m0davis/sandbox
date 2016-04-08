open import Agda.Builtin.Nat using (Nat)

-- module application, no instance
import Agda.Builtin.FromNat

zero : Nat
zero = 0 -- error, no instance
