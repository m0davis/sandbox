--{-# OPTIONS --show-implicit #-}
module Scratch where

module Maybes where
  open import Prelude

  postulate
    P : Set
    search : Maybe P

  unMaybe : ∀ {a} {A : Set a} (m : Maybe A) {_ : IsJust m} -> A
  unMaybe nothing {}
  unMaybe (just x) {_} = x

  proof : P
  proof = unMaybe search

{-
module Issue1555 where
  open import Agda.Builtin.Unit

  test : {
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    : ⊤} → ⊤ → ⊤
  test tt = tt
-}

-- module ContentedList where
--   open import Prelude

--   data CList {a} (A : Set a) : List A → Set a where
--     []  : CList A []
--     _∷_ : (x : A) {ls : List A} (xs : CList A ls) → CList A (x ∷ ls)

--   csingleton : {a : Level} {A : Set a} (x : A) → CList A (x ∷ [])
--   csingleton x = x ∷ []

--   chead : {a : Level} {A : Set a} {x : A} {ls : List A} → CList A (x ∷ ls) → Σ A λ x' → x' ≡ x
--   chead (x ∷ _) = x , refl

-- module StandardLibrary where
--   --open import Everything

-- module No-eta-equality₁ where

--   open import Prelude.Equality

--   record Σ (A : Set) (B : A -> Set) : Set where
--      no-eta-equality
--      constructor _,_
--      field
--        fst : A
--        snd : B fst

--   open Σ

--   fail : ∀ {A : Set}{B : A -> Set} → (x : Σ A B) → x ≡ (fst x , snd x)
--   fail x = {!refl!}

--   -- x != fst x , snd x of type Σ .A .B
--   -- when checking that the expression refl has type x ≡ (fst x , snd x)

-- module No-eta-equality₂ where
--   open import Agda.Builtin.Equality

--   record Pair-η= (A B : Set) : Set where
--     constructor _,_
--     field
--       fst : A
--       snd : B

--   test-η= : ∀ {A B : Set} → (p : Pair-η= A B) → Pair-η=.fst p , Pair-η=.snd p ≡ p
--   test-η= p = refl

--   record Pair-η≠ (A B : Set) : Set where
--     no-eta-equality
--     constructor _,_
--     field
--       fst : A
--       snd : B

--   test-η≠ : ∀ {A B : Set} → (p : Pair-η≠ A B) → Pair-η≠.fst p , Pair-η≠.snd p ≡ p
--   test-η≠ p = {!!}

--   test₂-η≠ : ∀ {A B : Set} → (a : A) (b : B) → (Pair-η≠._,_ a b) ≡ (a , b)
--   test₂-η≠ a b = refl

--   data Pair-data (A B : Set) : Set where
--     _,_ : A → B → Pair-data A B

--   fst : ∀ {A B : Set} → Pair-data A B → A
--   fst (a , b) = a

--   snd : ∀ {A B : Set} → Pair-data A B → B
--   snd (a , b) = b

--   test-data : ∀ {A B : Set} → (p : Pair-data A B) → fst p , snd p ≡ p
--   test-data p = {!!}

-- {-
-- module Test-Permutation where
--   --open import Data.Vec
--   --open import Relation.Binary
--   open import Data.Permutation
--   open import Data.Fin
--   open import Data.Nat

--   fin : Fin 3
--   fin = # 1

--   perm : Permutation 1
--   perm = fromℕ 0 ∷ []
-- -}

-- module ShowExtendedLambda where
--   open import Prelude

--   data D : Set where
--     d₀ : D
--     d₁ : Nat → D
--     d₂ : String → Nat → D → D

--   example-of-patlam : D → D
--   example-of-patlam d₀ = d₁ 0
--   example-of-patlam (d₁ n) = d₀
--   example-of-patlam (d₂ s n d) = case d of λ
--     { d₀ → d₁ 1
--     ; (d₁ x) → d₁ n
--     ; (d₂ s n d) → d₁ n
--     }

--   open import Tactic.Reflection
--   open import Tactic.Reflection.Quote

--   macro
--     showDef : Name → Tactic
--     showDef n hole = do
--       cs ← getClauses n -|
--       typeError [ termErr (` cs) ]

--   data C : Set where
--     c : C

--   foo : Set
--   foo = {!showDef example-of-patlam!}
-- {-
-- module CannotInstantiateMetavariable where
--   open import Prelude using (∃)
--   postulate
--     M : Set → Set
--     bind : ∀ {𝑨 𝑩 : Set} → M 𝑨 → (𝑨 → M 𝑩) → M 𝑩
--     bind' : ∀ {𝑨 : Set} {𝑩 : 𝑨 → Set} → M 𝑨 → ((a : 𝑨) → M (𝑩 a)) → ∃ λ a → M (𝑩 a)
--     A : Set
--     B : A → Set
--     action : (a : A) → M (B a)
--     MA : M A

--   foo : ∃ λ α → M (B α)
--   foo = --bind {A} {{!!}} MA {!action!}
--         bind' {A} {B} MA action
--   {-
--   Cannot instantiate the metavariable _53 to solution (B a) since it
--   contains the variable a which is not in scope of the metavariable
--   or irrelevant in the metavariable but relevant in the solution
--   when checking that the expression action has type A → M ?1
--   -}
-- -}
-- module UnsolvedMetas where
--   open import Prelude
--   postulate
--     M : Set → Set
--     instance
--       MonadM : Monad M
--       FunctorM : Functor M
--     A : Set
--     B : A → Set
--     action : (a : A) → M (B a)
--     mask : ∀ {a : A} → B a → A
--     MA : M A
--     c : A

--   foo : M (A × A)
--   foo = MA >>= λ ma → action ma >>= λ b → return (mask b , c)

--   data Masked : Set where
--     mask' : ∀ {a : A} → B a → Masked

--   bar : M _
--   bar = do
--     ma ← MA -|
--     b ← action ma -|
--     b' ← mask' <$> action ma -|
--     return (b' , mask' b , c)
