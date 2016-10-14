--{-# OPTIONS -v profile:10 #-}
open import Agda.Builtin.Reflection
open import Postlude
module Map-InternalError where

record R : Set₁ where
  foo : Set
  foo = ∀ {x} → {!!}

  field
    bar : Set
