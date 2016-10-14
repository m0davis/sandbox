module Map-InternalError-2 where

record R (A : Set) : Set₁ where
  field
    a : A
    F : ∀ {f} → Set

  foo : Set
  foo = ∀ {f} → {!!}

  field
    bar : Set
