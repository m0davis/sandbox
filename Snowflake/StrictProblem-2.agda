module Snowflake.StrictProblem-2 where

module M₁ where
  open import Agda.Builtin.Strict using (primForce; primForceLemma)
  open import Agda.Builtin.Nat using (Nat; zero; suc)
  open import Agda.Builtin.Equality using (_≡_; refl)

  infixr 0 _$!_
  _$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
  f $! x = primForce x f

  _$=_ : ∀ {a b} {A : Set a} {B : A → Set b} (f : ∀ x → B x) (x : A) → primForce x f ≡ f x
  f $= x = primForceLemma x f

  data Wrap : Nat → Set where
    wrap : (n : Nat) → Wrap n

  data Dup : Nat → Set where
    zero  : Dup zero
    suc : ∀ {n : Nat} → Dup (suc n)

  unwrap : ∀ {n : Nat} → Wrap n → Nat
  unwrap (wrap 0) = 0
  unwrap (wrap (suc n)) = Nat.suc $! (unwrap (wrap n))

  subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P y → P x
  subst P refl px = px

  wrap→dup : ∀ {n : Nat} → (w : Wrap n) → Dup (unwrap w)
  wrap→dup (wrap 0) = zero
  wrap→dup (wrap (suc n)) = subst Dup (suc $= (unwrap (wrap n))) suc
  --wrap→dup (wrap (suc n)) = suc
  {- ERROR:
       suc (_n_34 n) != primForce (unwrap (wrap n)) suc of type Nat
       when checking that the expression suc has type
       Dup (unwrap (wrap (suc n)))

     No error if the strictness application is removed from 'unwrap'.
  -}

module M₂ where
  open import Agda.Builtin.Strict using (primForce; primForceLemma)
  open import Agda.Builtin.Nat using (Nat; zero; suc)
  open import Agda.Builtin.Equality using (_≡_; refl)

  infixr 0 _$!_
  _$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
  f $! x = primForce x f

  _$=_ : ∀ {a b} {A : Set a} {B : A → Set b} (f : ∀ x → B x) (x : A) → primForce x f ≡ f x
  f $= x = primForceLemma x f

  data Dup : Nat → Set where
    zero  : Dup zero
    suc : ∀ {n : Nat} → Dup (suc n)

  unwrap : Nat → Nat
  unwrap 0 = 0
  unwrap (suc n) = suc $! (unwrap n)

  subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P y → P x
  subst P refl px = px

  wrap→dup : (w : Nat) → Dup (unwrap w)
  wrap→dup 0 = zero
  wrap→dup (suc n) = subst Dup (suc $= (unwrap n)) suc
  --wrap→dup (suc n) = suc
  {- ERROR:
       suc (_n_127 n) != primForce (unwrap n) suc of type Nat
       when checking that the expression suc has type Dup (unwrap (suc n))

     No error if the strictness application is removed from 'unwrap'.
  -}
  {-
    Dup (unwrap w) -->
      Dup (primForce (unwrap n) suc)

    primForceLemma (unwrap n) suc : primForce (unwrap n) suc ≡ suc (unwrap n)

    suc : ∀ {n : Nat} → Dup (suc n)
    subst Dup (suc $= (unwrap n)) -->
      subst Dup (primForceLemma (unwrap n) suc) : Dup (primForce (unwrap n) suc)



  -}
