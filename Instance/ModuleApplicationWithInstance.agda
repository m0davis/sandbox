open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

-- no module application and no instance, yet

before : 0 ≡ zero
before = refl

-- module application and instance
open import Instance using ()

after : 0 ≡ suc zero
after = refl

open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.Nat     using (Nat; suc)

-- the instance is in scope
NumberNat+1 : Number Nat
NumberNat+1 = Instance.NumberNat+1
