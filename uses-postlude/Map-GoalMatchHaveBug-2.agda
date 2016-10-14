{-# OPTIONS --show-implicit #-}
postulate
  F : Set₁ → Set₁
  prove-F : ∀ ..{A : Set₁} (x : A) → F A
  X : Set
  G : X → Set
  explicit : X → Set
  implicit : {x : X} → G x → Set

test-explicit : F (X → Set)
test-explicit = prove-F explicit

test-implicit-fails : F (∀ {x : X} → G x → Set)
test-implicit-fails = prove-F {_} (λ {_} → implicit)
                              -- Goal: {x : X} → G x → Set
                              -- Have: {x : X} → G x → Set

test-implicit-works : F (∀ {x : X} → G x → Set)
test-implicit-works = prove-F (λ {x} → implicit {x})

test-implicit-works-2 : ∀ {x : X} → G x → Set
test-implicit-works-2 = {!implicit!}

record R : Set₁ where
  field
    foo : ∀ {x : X} → G x → Set
    R-prove-F : F (∀ {x : X} → G x → Set)

r : R
r =
  record
  { foo = implicit
  ; R-prove-F = prove-F {!implicit!}
  }

{-
`agda2-goal-and-context-and-inferred`:
  Goal: {x : X} → Set
  Have: {_ : X} → Set

① : (∀ {x : A} → B)    is-the-same-as  ({x : A} → B)
② : (∀ {x} → B)        is-the-same-as  ({x : _} → B)
③ : (∀ {x y} → B)      is-the-same-as  (∀ {x} → ∀ {y} → B)


-}
