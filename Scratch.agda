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
