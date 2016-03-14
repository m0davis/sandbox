module AgdaPreludeIssue28 where

  module EquivalenceOf≤ where
    open import Agda.Builtin.Equality
    open import Agda.Builtin.Nat
    
    open import Data.Nat using (less-than-or-equal) renaming (_≤_ to _≤ₛ_)
    open import Data.Nat.Properties using (≤⇒≤″; ≤″⇒≤)
    open import Prelude using (diff) renaming (_≤_ to _≤ₚ_)

    open import Tactic.Nat using (by)

    ≤ₚ→≤ₛ : ∀ {a b} → a ≤ₚ b → a ≤ₛ b
    ≤ₚ→≤ₛ (diff k b₊₁≡k₊₁+a) = ≤″⇒≤ (less-than-or-equal {k = k} (by b₊₁≡k₊₁+a))
   
    ≤ₛ→≤ₚ : ∀ {a b} → a ≤ₛ b → a ≤ₚ b
    ≤ₛ→≤ₚ a≤ₛb with ≤⇒≤″ a≤ₛb
    ≤ₛ→≤ₚ _ | less-than-or-equal {k = k} a+k≡b = diff k (by a+k≡b)

  module AgdaPreludeTest where
    open import Prelude
    open import Tactic.Nat.Adapter (quote _≤_) (quote id) (quote id)

    auto-example₁ : (a b : Nat) → (a - b) * (a + b) ≡ a ^ 2 - b ^ 2
    auto-example₁ a b = auto
   
    auto-example₂ : (a b : Nat) → (a + b) ^ 2 ≥ a ^ 2 + b ^ 2
    auto-example₂ a b = auto

    by-example₁ : (xs ys : List Nat) → sum (xs ++ ys) ≡ sum ys + sum xs
    by-example₁ []       ys = auto
    by-example₁ (x ∷ xs) ys = by (by-example₁ xs ys)
   
    by-example₂ : (a b c : Nat) → a + c < b + c → a < b
    by-example₂ a b c lt = by lt
   
    by-example₃ : (a b : Nat) → a ≡ b * 2 → a + b < (b + 1) * 3
    by-example₃ a b eq = by eq
   
    by-example₄ : (a b c : Nat) → a + b + c ≤ b → 2 * c ≡ c
    by-example₄ a b c lt = by lt

    refute-example₁ : {Anything : Set} (a : Nat) → a ≡ 2 * a + 1 → Anything
    refute-example₁ a eq = refute eq
   
    refute-example₂ : {Anything : Set} (a b : Nat) → a + b < a → Anything
    refute-example₂ a b lt = refute lt

    simplify-goal-example₁ : (a b : Nat) → a - b ≡ b - a → a ≡ b
    simplify-goal-example₁  zero    b      eq = by eq
    simplify-goal-example₁ (suc a)  zero   eq = refute eq
    simplify-goal-example₁ (suc a) (suc b) eq =
      simplify-goal (simplify-goal-example₁ a b eq)

    simplify-goal-example₂ : (a b : Nat) → a - b ≡ b - a → a < suc b
    simplify-goal-example₂  zero    b      eq = by eq
    simplify-goal-example₂ (suc a)  zero   eq = refute eq
    simplify-goal-example₂ (suc a) (suc b) eq =
      simplify-goal (simplify-goal-example₂ a b eq)

    lemma₁ : (a b : Nat) → a + b ≡ 0 → a ≡ 0
    lemma₁ zero    b eq = refl
    lemma₁ (suc a) b eq = refute eq
   
    simplify-example₁ : ∀ a b → (a + 1) * (b + 1) ≡ a * b + 1 → a ≡ 0
    simplify-example₁ a b eq = simplify eq λ eq′ → lemma₁ a b eq′
   
    lemma₂ : (a b : Nat) → a + b ≡ 0 → a < suc 0
    lemma₂ zero    b eq = auto
    lemma₂ (suc a) b eq = refute eq
   
    simplify-example₂ : ∀ a b → (a + 1) * (b + 1) ≡ a * b + 1 → a < suc 0
    simplify-example₂ a b eq = simplify eq λ eq′ → by (lemma₂ a b eq′)

    downFrom' : Nat → List Nat
    downFrom' zero    = []
    downFrom' (suc n) = suc n ∷ downFrom' n

    induction-example₁ : ∀ n → sum (downFrom' n) * 2 ≡ n * (n + 1)
    induction-example₁ = induction

    induction-example₂ : ∀ n → sum (downFrom' n) * 2 < suc (n * (n + 1))
    induction-example₂ = induction
    
  module StandardLibraryTest where
    open import Agda.Builtin.Equality
    open import Data.Nat
    open import Data.List
    open import Function

    infixr 8 _^_
    _^_ : ℕ → ℕ → ℕ
    n ^ zero  = 1
    n ^ suc m = n ^ m * n
    
    open EquivalenceOf≤
    open import Tactic.Nat.Adapter (quote _≤_) (quote ≤ₛ→≤ₚ) (quote ≤ₚ→≤ₛ)

    auto-example₁ : (a b : ℕ) → (a ∸ b) * (a + b) ≡ a ^ 2 ∸ b ^ 2
    auto-example₁ a b = auto
   
    auto-example₂ : (a b : ℕ) → (a + b) ^ 2 ≥ a ^ 2 + b ^ 2
    auto-example₂ a b = auto

    by-example₁ : (xs ys : List ℕ) → sum (xs ++ ys) ≡ sum ys + sum xs
    by-example₁ []       ys = auto
    by-example₁ (x ∷ xs) ys = by (by-example₁ xs ys)
   
    by-example₂ : (a b c : ℕ) → a + c < b + c → a < b
    by-example₂ a b c lt = by lt
   
    by-example₃ : (a b : ℕ) → a ≡ b * 2 → a + b < (b + 1) * 3
    by-example₃ a b eq = by eq
   
    by-example₄ : (a b c : ℕ) → a + b + c ≤ b → 2 * c ≡ c
    by-example₄ a b c lt = by lt

    refute-example₁ : {Anything : Set} (a : ℕ) → a ≡ 2 * a + 1 → Anything
    refute-example₁ a eq = refute eq
   
    refute-example₂ : {Anything : Set} (a b : ℕ) → a + b < a → Anything
    refute-example₂ a b lt = refute lt

    simplify-goal-example₁ : (a b : ℕ) → a ∸ b ≡ b ∸ a → a ≡ b
    simplify-goal-example₁  zero    b      eq = by eq
    simplify-goal-example₁ (suc a)  zero   eq = refute eq
    simplify-goal-example₁ (suc a) (suc b) eq =
      simplify-goal (simplify-goal-example₁ a b eq)

    simplify-goal-example₂ : (a b : ℕ) → a ∸ b ≡ b ∸ a → a < suc b
    simplify-goal-example₂  zero    b      eq = by eq
    simplify-goal-example₂ (suc a)  zero   eq = refute eq
    simplify-goal-example₂ (suc a) (suc b) eq =
      simplify-goal (by (simplify-goal-example₂ a b eq))

    lemma₁ : (a b : ℕ) → a + b ≡ 0 → a ≡ 0
    lemma₁ zero    b eq = refl
    lemma₁ (suc a) b eq = refute eq
   
    simplify-example₁ : ∀ a b → (a + 1) * (b + 1) ≡ a * b + 1 → a ≡ 0
    simplify-example₁ a b eq = simplify eq λ eq′ → lemma₁ a b eq′
   
    lemma₂ : (a b : ℕ) → a + b ≡ 0 → a < suc 0
    lemma₂ zero    b eq = s≤s z≤n
    lemma₂ (suc a) b eq = refute eq
   
    simplify-example₂ : ∀ a b → (a + 1) * (b + 1) ≡ a * b + 1 → a < suc 0
    simplify-example₂ a b eq = simplify eq λ eq′ → by (lemma₂ a b eq′)

    downFrom' : ℕ → List ℕ
    downFrom' zero    = []
    downFrom' (suc n) = suc n ∷ downFrom' n

    induction-example₁ : ∀ n → sum (downFrom' n) * 2 ≡ n * (n + 1)
    induction-example₁ = induction

    induction-example₂ : ∀ n → sum (downFrom' n) * 2 < suc (n * (n + 1))
    induction-example₂ = induction
