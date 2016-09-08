{-# OPTIONS --show-implicit #-}
module AgdaIssue-CaseSplitBug-2166 where

module M₁ where
  data D : Set₁ where
    d : ∀ {A : Set} → A → D

  foo : D → Set
  foo (d {A = A} x) = {!!}

module M₂ where
  data 𝕃 {𝑨} (𝐴 : Set 𝑨) : Set 𝑨

  data 𝕃 {𝑨} (𝐴 : Set 𝑨) where
    ∅ : 𝕃 𝐴
    ✓ : {x₁s : 𝕃 𝐴} → 𝕃 𝐴 → 𝕃 𝐴

  bar : ∀ {𝑨} {𝐴 : Set 𝑨} (xs : 𝕃 𝐴) → Set
  bar {𝑨} {𝐴} xs = {!xs!}

module M₃ where
  data W : Set where
    w : W
  data L : W → Set where
    ∅ : L w
    ✓ : {x : W} → L x → L w

  qux : L w → Set
  qux ∅ = {!!}
  qux (✓ {x = x} xs) = {!!}

module M₄ where
  data D : Set where
    d : {x : D} → D

  f : D → Set
  f y = {!y!}
  {- case split on y yields:
       f (d {y = y}) = ?
     which is an error (wrong implicit variable name)
  -}
