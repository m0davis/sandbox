--{-# OPTIONS --show-implicit #-}
module Scratch where

module StandardLibrary where
  open import Data.Vec

module ShowExtendedLambda where
  open import Prelude

  data D : Set where
    d₀ : D
    d₁ : Nat → D
    d₂ : String → Nat → D → D

  example-of-patlam : D → D
  example-of-patlam d₀ = d₁ 0
  example-of-patlam (d₁ n) = d₀
  example-of-patlam (d₂ s n d) = case d of λ
    { d₀ → d₁ 1
    ; (d₁ x) → d₁ n
    ; (d₂ s n d) → d₁ n
    }

  open import Tactic.Reflection
  open import Tactic.Reflection.Quote

  macro
    showDef : Name → Tactic
    showDef n hole = do
      cs ← getClauses n -|
      typeError [ termErr (` cs) ]

  data C : Set where
    c : C

  foo : Set
  foo = {!showDef example-of-patlam!}

module CannotInstantiateMetavariable where
  postulate
    I : Set → Set
    bind : ∀ {𝑨 𝑩 : Set} → I 𝑨 → (𝑨 → I 𝑩) → I 𝑩
    A : Set
    B : A → Set
    action : (a : A) → I (B a)
    IA : I A

  foo : I (∀ {α : A} → B α)
  foo = bind {A} {{!_!}} IA {!action!}
  {-
  Cannot instantiate the metavariable _53 to solution (B a) since it
  contains the variable a which is not in scope of the metavariable
  or irrelevant in the metavariable but relevant in the solution
  when checking that the expression action has type A → I ?1  
  -}
