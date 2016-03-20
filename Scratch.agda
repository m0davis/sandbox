--{-# OPTIONS --show-implicit #-}
module Scratch where

module StandardLibrary where
  open import Data.Vec
  open import Relation.Binary

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
  open import Prelude using (∃)
  postulate
    M : Set → Set
    bind : ∀ {𝑨 𝑩 : Set} → M 𝑨 → (𝑨 → M 𝑩) → M 𝑩
    bind' : ∀ {𝑨 : Set} {𝑩 : 𝑨 → Set} → M 𝑨 → ((a : 𝑨) → M (𝑩 a)) → ∃ λ a → M (𝑩 a)
    A : Set
    B : A → Set
    action : (a : A) → M (B a)
    MA : M A

  foo : ∃ λ α → M (B α)
  foo = --bind {A} {{!!}} MA {!action!}
        bind' {A} {B} MA action
  {-
  Cannot instantiate the metavariable _53 to solution (B a) since it
  contains the variable a which is not in scope of the metavariable
  or irrelevant in the metavariable but relevant in the solution
  when checking that the expression action has type A → M ?1  
  -}

module UnsolvedMetas where
  open import Prelude
  postulate
    M : Set → Set
    instance
      MonadM : Monad M
      FunctorM : Functor M
    A : Set
    B : A → Set
    action : (a : A) → M (B a)    
    mask : ∀ {a : A} → B a → A
    MA : M A
    c : A

  foo : M (A × A)
  foo = MA >>= λ ma → action ma >>= λ b → return (mask b , c)

  data Masked : Set where
    mask' : ∀ {a : A} → B a → Masked

  bar : M _
  bar = do
    ma ← MA -|
    b ← action ma -|
    b' ← mask' <$> action ma -|
    return (b' , mask' b , c)
