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

  open import Agda.Builtin.Reflection using (Name)
  module Adapter (`_≤ₐ_ `≤ₐ→≤₀ `≤₀→≤ₐ : Name) where
    open import Prelude
    open import Tactic.Reflection
    open import Data.Nat using () renaming (_≤_ to _≤ₛ_)
    open import Tactic.Nat hiding (by) public
   
    macro
      by : Term → Tactic
      by prfₐ holeₐ = do
        goalₐ ← inferType holeₐ -|
        hole₀ := a→0 goalₐ holeₐ -|
        Prfₐ ← inferType prfₐ -|
        prf₀ := a→0 Prfₐ prfₐ -|
        unify holeₐ ∘ 0→a goalₐ =<< by-tactic prf₀ =<< inferType =<< normalise hole₀
          
        where

        a→0 : Type → Term → Term
        a→0 (def operator _) = ifYes operator == `_≤ₐ_ then def₁ `≤ₐ→≤₀ else id
        a→0 _ = id -- TODO
            
        0→a : Type → Term → Term
        0→a (def operator _) = ifYes operator == `_≤ₐ_ then def₁ `≤₀→≤ₐ else id
        0→a _ = id -- TODO
        
  module StandardLibraryTest where
    open import Agda.Builtin.Equality
    open import Data.Nat
    open import Data.List

    infixr 8 _^_
    _^_ : ℕ → ℕ → ℕ
    n ^ zero  = 1
    n ^ suc m = n ^ m * n
    
    open EquivalenceOf≤
    open Adapter (quote _≤_) (quote ≤ₛ→≤ₚ) (quote ≤ₚ→≤ₛ)

    auto-example₁ : (a b : ℕ) → (a ∸ b) * (a + b) ≡ a ^ 2 ∸ b ^ 2
    auto-example₁ a b = {!auto!}
   
    auto-example₂ : (a b : ℕ) → (a + b) ^ 2 ≥ a ^ 2 + b ^ 2
    auto-example₂ a b = {!auto!}

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
    refute-example₁ a eq = {!refute eq!}
   
    refute-example₂ : {Anything : Set} (a b : ℕ) → a + b < a → Anything
    refute-example₂ a b lt = {!refute lt!}

    simplify-goal-example : (a b : ℕ) → a ∸ b ≡ b ∸ a → a ≡ b
    simplify-goal-example  zero    b      eq = by eq
    simplify-goal-example (suc a)  zero   eq = {!refute eq!}
    simplify-goal-example (suc a) (suc b) eq =
      {!simplify-goal (simplify-goal-example a b eq)!}

    lemma : (a b : ℕ) → a + b ≡ 0 → a ≡ 0
    lemma zero    b eq = refl
    lemma (suc a) b eq = {!refute eq!}
   
    simplify-example : ∀ a b → (a + 1) * (b + 1) ≡ a * b + 1 → a ≡ 0
    simplify-example a b eq = {!simplify eq λ eq′ → lemma a b eq′!}
   
    induction-example : ∀ n → sum (downFrom n) * 2 ≡ n * (n + 1)
    induction-example = {!induction!}

