module Instance.Main where

open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

before : 0 ≡ zero
before = refl

open import Instance.NumberNat+1 using ()

after : 0 ≡ suc zero
after = refl

open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.Nat     using (Nat; suc)

NumberNat+1 : Number Nat
NumberNat+1 = Instance.NumberNat+1.NumberNat+1
