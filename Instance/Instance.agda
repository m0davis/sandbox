open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.Nat     using (Nat; suc)
open import Agda.Builtin.Unit    using (⊤)

instance
  NumberNat+1 : Number Nat
  Number.Constraint NumberNat+1 _ = ⊤
  Number.fromNat    NumberNat+1 n = suc n
