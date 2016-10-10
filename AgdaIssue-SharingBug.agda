data ⊥ : Set where

infix 4 ¬_
¬_ : ∀ {a} (A : Set a) → Set a
¬ A = A → ⊥

data Dec {a} (P : Set a) : Set a where
  yes : P → Dec P
  no  : ¬ P → Dec P

open import Agda.Builtin.Equality

record Eq {a} (A : Set a) : Set a where
  infix 4 _==_
  field
    _==_ : (x y : A) → Dec (x ≡ y)

open Eq {{...}}

open import Agda.Builtin.Bool

instance
  EqBool : Eq Bool
  _==_ {{EqBool}} false false = yes refl
  _==_ {{EqBool}} false true  = no λ () -- fails to solve constraints...
  _==_ {{EqBool}} true  false = no λ () -- ...and results in unsolved metas
  _==_ {{EqBool}} true  true  = yes refl
