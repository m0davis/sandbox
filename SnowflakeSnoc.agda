open import Prelude
  using ( ⊥
        ; ¬_
        ; _≡_
        )

_≢_ : ∀ {a} {A : Set a} → A → A → Set a
A ≢ B = ¬ A ≡ B

module SnowflakeSnoc where
  data SnowflakeSnoc {a} (A : Set a) : Set a
  data _∉_ {a} {A : Set a} (x : A) : SnowflakeSnoc A → Set a

  data SnowflakeSnoc {a} (A : Set a) where
    ε : SnowflakeSnoc A
    φ : ∀ {x} {xs : SnowflakeSnoc A} (x∉xs : x ∉ xs) → SnowflakeSnoc A

  data _∉_ {a} {A : Set a} (x : A) where
    ε : x ∉ ε
    φ : ∀ {x' xs'} → (x'∉xs' : x' ∉ xs') → x ≢ x' → x ∉ (φ x'∉xs')

  _∈_ : ∀ {a} {A : Set a} (x : A) (xs : SnowflakeSnoc A) → Set a
  x ∈ xs = ¬ x ∉ xs

  _++_ : ∀ {a} {A : Set a} → {xs : SnowflakeSnoc A} (ys : SnowflakeSnoc A) → (∀ {u} → u ∈ xs → u ∉ ys) → SnowflakeSnoc A
  ys ++ x = {!!}
