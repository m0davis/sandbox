module AgdaIssue1890 where
  open import Prelude
  open import Tactic.Reflection

  module _ (A : Set) where
    record R : Set where

    `R₀ : Type
    `R₀ = def₀ (quote R)

    `R₁ : Term → Type
    `R₁ = def₁ (quote R)

    `Nat : Type
    `Nat = def₀ (quote Nat)

    helper-type₀ : Type
    helper-type₀ = `R₀ `→ `R₀

    helper-type₁ : Type
    helper-type₁ = `R₁ `Nat `→ `R₁ `Nat

    helper-term : Term
    helper-term = var₀ 0

    helper-patterns : List (Arg Pattern)
    helper-patterns = vArg (var "_") ∷
                      []

    macro
      mac₀ : Tactic
      mac₀ hole =
        n ← freshName "n" -|
        define (vArg n) helper-type₀ (clause helper-patterns helper-term ∷ []) ~|
        typeError [ strErr "definition succeeded" ]

      mac₁ : Tactic
      mac₁ hole =
        n ← freshName "n" -|
        define (vArg n) helper-type₁ (clause helper-patterns helper-term ∷ []) ~|
        typeError [ strErr "definition succeeded" ]

    within-module-succeeds₀ : Set
    within-module-succeeds₀ = {!mac₀!}

    within-module-fails₁ : Set
    within-module-fails₁ = {!mac₁!}

  outside-module-fails₀ : Set
  outside-module-fails₀ = {!mac₀ Nat!}

  outside-module-succeeds₁ : Set
  outside-module-succeeds₁ = {!mac₁ Nat!}
