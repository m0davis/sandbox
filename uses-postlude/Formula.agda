module Formula where
  open import Prelude
  --postulate C : Set
  record Listlike (A : Set) : Set where
    inductive
    field
      listdestruct : Either A (Listlike A)
  data Expression (Symbol : Set) (Container : Set → Listlike (Expression Symbol)) : Set where
    atomic : Symbol → Expression Symbol
    compound : Symbol → Listlike (Expression Symbol) → Expression Symbol
