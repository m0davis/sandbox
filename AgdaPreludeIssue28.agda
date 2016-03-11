module AgdaPreludeIssue28 where

  module EquivalenceOf<And≤ where
    open import Agda.Builtin.Equality
    open import Agda.Builtin.Nat
    
    open import Data.Nat using (less-than-or-equal) renaming (_<_ to _<ₛ_ ; _≤_ to _≤ₛ_)
    open import Data.Nat.Properties using (≤⇒≤″; ≤″⇒≤)
    open import Prelude using (diff) renaming (_<_ to _<ₚ_ ; _≤_ to _≤ₚ_)

    open import Tactic.Nat using (by)

    ≤ₚ→≤ₛ : ∀ {a b} → a ≤ₚ b → a ≤ₛ b
    ≤ₚ→≤ₛ (diff k b₊₁≡k₊₁+a) = ≤″⇒≤ (less-than-or-equal {k = k} (by b₊₁≡k₊₁+a))
   
    ≤ₛ→≤ₚ : ∀ {a b} → a ≤ₛ b → a ≤ₚ b
    ≤ₛ→≤ₚ a≤ₛb with ≤⇒≤″ a≤ₛb
    ≤ₛ→≤ₚ _ | less-than-or-equal {k = k} a+k≡b = diff k (by a+k≡b)

    <ₚ→<ₛ : ∀ {a b} → a <ₚ b → a <ₛ b
    <ₚ→<ₛ (diff k b₊₁≡k₊₁+a) = ≤″⇒≤ (less-than-or-equal {k = k} (by b₊₁≡k₊₁+a))
   
    <ₛ→<ₚ : ∀ {a b} → a <ₛ b → a <ₚ b
    <ₛ→<ₚ a≤ₛb with ≤⇒≤″ a≤ₛb
    <ₛ→<ₚ _ | less-than-or-equal {k = k} a+k≡b = diff k (by a+k≡b)

  open import Agda.Builtin.Reflection using (Name)
  open import Agda.Builtin.Nat using (Nat)
  module Adapter (`_<ₐ_ `<ₐ→<₀ `<₀→<ₐ `_≤ₐ_ `≤ₐ→≤₀ `≤₀→≤ₐ : Name) where
    open import Prelude
    open import Tactic.Reflection
    open import Data.Nat using () renaming (_<_ to _<ₛ_; _≤_ to _≤ₛ_)
    open import Tactic.Nat hiding (by) public
    open import Tactic.Reflection.Quote
    open import Tactic.Reflection.Match
   
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
        a→0 (def operator _) = 
          ifYes operator == `_<ₐ_ then def₁ `<ₐ→<₀ else
          ifYes operator == `_≤ₐ_ then def₁ `≤ₐ→≤₀ else
                                       id
        a→0 _ = id -- TODO
            
        0→a : Type → Term → Term
        0→a (def operator _) = 
          ifYes operator == `_<ₐ_ then def₁ `<₀→<ₐ else
          ifYes operator == `_≤ₐ_ then def₁ `≤₀→≤ₐ else
                                       id
        0→a _ = id -- TODO
        
  module StandardLibraryTest where
    open import Data.Nat
    open import Agda.Builtin.Equality
    open EquivalenceOf<And≤
    open Adapter (quote _<_) (quote <ₛ→<ₚ) (quote <ₚ→<ₛ) (quote _≤_) (quote ≤ₛ→≤ₚ) (quote ≤ₚ→≤ₛ)

    open import Agda.Builtin.Reflection
    open import Agda.Builtin.List

    by-example₄ : (a b c : ℕ) → a + b + c ≤ b → 2 * c ≡ c
    by-example₄ a b c lt = by lt

    test-byₛ : {a b : ℕ} → suc a ≤ b → a ≤ suc b
    test-byₛ a₊₁≤b = by a₊₁≤b

    downFrom : Nat → List Nat
    downFrom zero    = []
    downFrom (suc n) = suc n ∷ downFrom n
{-    
    induction-example : ∀ n → sum (downFrom n) Data.Nat.* 2 ≡ n Data.Nat.* (n Data.Nat.+ 1)
    induction-example = induction
-}    

    _^_ : Nat → Nat → Nat
    n ^ zero  = 1
    n ^ suc m = n ^ m * n
    
--    auto-example₁ : (a b : Nat) → (a - b) * (a + b) ≡ ((a ^ 2) - (b ^ 2))
--    auto-example₁ a b = auto
