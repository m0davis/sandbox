module AgdaIssue1890-2 where
  open import Prelude
  open import Tactic.Reflection

  postulate
    trustMe : ∀ {α} {A : Set α} → A

  macro
    trust-the-doppelganger : Tactic
    trust-the-doppelganger hole = do
      telescope ← reverse <$> getContext -|
      goal ← inferType hole -|
      nameₕ ← freshName "nameₕ" -|
      catchTC
        (define (vArg nameₕ) (telPi telescope goal) [ clause (telePat telescope) (def₀ (quote trustMe)) ])
        (typeError (strErr "failed defining a function with type" ∷ termErr (telPi telescope goal) ∷ []))
        ~|
      unify hole (def nameₕ (teleArgs telescope))

  module M₀ where
    postulate
      P : Set
   
    no-param-succeeds : P
    no-param-succeeds = trust-the-doppelganger

  module M₁ (A : Set) where
    postulate
      P : Set

    inside-M₁-fails : P
    inside-M₁-fails = trust-the-doppelganger -- failed defining a function with type (A₁ : Set) → P A₁

  outside-M₁-succeeds : (A : Set) → M₁.P A
  outside-M₁-succeeds = trust-the-doppelganger
