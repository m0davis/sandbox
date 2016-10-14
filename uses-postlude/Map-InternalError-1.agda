module Map-InternalError-1 where

record R : Set₁ where
  foo : Set
  foo = ∀ {f} → {!!}

  field
    bar : Set
