postulate
  A : Set
  B : A → Set
  x : A
  y : B x

record R : Set where
  constructor c
  field
    {a} : A
    {b} : B a

works : R
works = c {b = y}

fails : R
fails = {!!} -- record { b = y }
-- Agda expects a type of A instead of B .a

postulate
  K : Set
  V : K → Set
  Carrier : Set

open import Tactic.Reflection.Reright

record Map : Set₁ where
  field
    _∈_ : K → Carrier → Set

    _∉_ : K → Carrier → Set

  field
    ∅-is-empty : ∀ {𝑘} {∅ : Carrier} → 𝑘 ∉ ∅
    get : ∀ {k : K} {m : Carrier} → k ∈ m → V k

  postulate
    implicit : ∀ {k : K} → Set
    im : (x : Carrier) → ∀ {k} → k ∈ x → k ∈ x

  record R'' (x : Carrier) : Set₁ where
    field
      foo : ∀ {k} → k ∈ x → k ∈ x -- x ⊆ z

  [_∪_] : (x : Carrier) → R'' x
  [_∪_] x = record { foo = im x }

{-
postulate
  R' : Carrier → Set
  _∈'_ : K → Carrier → Set
  im' : (x : Carrier) → ∀ {k} → k ∈' x → Set

foo' : {x : Carrier} → R' x → ∀ {k} → k ∈' x → Set
foo' {x} r = im' x
-}

postulate
  R' : Set
  F : Carrier → Set
  im' : (x : Carrier) → ∀ {k : K} → F x → Set

foo' : (x : Carrier) → R' → ∀ {k : K} → F x → Set
foo' x = λ r {k} → im' x {k}
