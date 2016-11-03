--{-# OPTIONS --no-positivity-check #-}
module Free where
  open import Postlude
{-
  data D : Set₁ where
    d : D → (Set → D) → D

  record R : Set₁ where
    inductive
    field
      r : (Set → R) → R

  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat
  record N : Set₁ where
    inductive
    field
      nzero? : Bool
      nsuc : nzero? ≡ false → (Nat → N) → N

  zero-N : N
  zero-N = record { nzero? = true ; nsuc = λ () }

  suc-N : Nat → N
  suc-N 0 = zero-N
  suc-N (suc n) = record { nzero? = false ; nsuc = λ { refl make-n → make-n n } }

  {-# TERMINATING #-}
  toNat : N → Nat
  toNat record { nzero? = true ; nsuc = nsuc } = 0
  toNat record { nzero? = false ; nsuc = nsuc } = suc (toNat (nsuc refl suc-N))

  test : toNat (suc-N 10) ≡ 10
  test = refl
-}

  data Free {𝑨 𝑩} (F : ∀ {𝑎} → Set 𝑎 → Set 𝑩) (A : Set 𝑨) : Set (sucₗ (𝑨 ⊔ₗ 𝑩)) where
    dpure : A → Free F A
    dfree : ∀ {𝑎 : Set 𝑨} → (𝑎 → Free F A) → F 𝑎 → Free F A

{-
  data Free {𝑨 𝑩} (F : ∀ {𝑎} → Set 𝑎 → Set 𝑩) (A : Set 𝑨) : Set (sucₗ (𝑨 ⊔ₗ 𝑩)) where
    dpure : A → Free F A
    dfree : F (Free F A) → Free F A
-}
  record Pure {𝑨} (A : Set 𝑨) : Set 𝑨 where
    field
      pure : A

  private
    module R-Type where
      data Type : Set where
        isPure : Type
        isFree : Type

  mutual
    record R-Free {𝑨 𝑩} (F : ∀ {𝑎} → Set 𝑎 → Set 𝑩) (A : Set 𝑨) : Set (sucₗ (𝑨 ⊔ₗ 𝑩)) where
      inductive
      open R-Type public

      field
        type : Type
        rPure : type ≡ isPure → Pure A
        rFree : type ≡ isFree → R-Free-Free F A

    record R-Free-Free {𝑨 𝑩} (F : ∀ {𝑎} → Set 𝑎 → Set 𝑩) (A : Set 𝑨) : Set (sucₗ (𝑨 ⊔ₗ 𝑩)) where
      inductive
      field
        {rFree-𝑎} : Set 𝑨
        rFree-f : rFree-𝑎 → R-Free F A
        rFree-m : F rFree-𝑎


  instance
    Free-RFree : ∀ {𝑨 𝑩} {F : ∀ {𝑎} → Set 𝑎 → Set 𝑩} {A : Set 𝑨} → Free F A → R-Free F A
    Free-RFree (dpure x) = record { type = R-Free.isPure ; rPure = λ _ → record { pure = x } ; rFree = λ () }
    Free-RFree (dfree {𝑎} x x₁) = record { type = R-Free.isFree ; rPure = λ () ; rFree = λ x₂ → record { rFree-𝑎 = 𝑎 ; rFree-f = λ x₃ → Free-RFree (x x₃) ; rFree-m = x₁ } }

  open import Prelude.Equality.Inspect

  {-# TERMINATING #-}
  toFree : ∀ {𝑨 𝑩} {F : ∀ {𝑎} → Set 𝑎 → Set 𝑩} {A : Set 𝑨} → R-Free F A → Free F A
  {-
  toFree x with R-Free.type x | graphAt R-Free.type x
  toFree x | R-Free.isPure | ingraph eq = dpure {!!}
  toFree x | R-Free.isFree | ingraph eq with R-Free.rFree x
  ... | y = dfree (λ x₁ → toFree (R-Free-Free.rFree-f (y eq) x₁)) (R-Free-Free.rFree-m (y eq))
  -}
  toFree record { type = R-Free.isPure ; rPure = rPure ; rFree = rFree } with rPure refl
  toFree record { type = R-Free.isPure ; rPure = rPure ; rFree = rFree } | record { pure = pure } = dpure pure
  toFree record { type = R-Free.isFree ; rPure = rPure ; rFree = rFree } = dfree (λ x → toFree (R-Free-Free.rFree-f (rFree refl) x)) (R-Free-Free.rFree-m (rFree refl))
  {-
  toFree record { type = R-Free.isFree ; rPure = rPure ; rFree = rFree } with rFree refl
  toFree record { type = R-Free.isFree ; rPure = rPure ; rFree = rFree } | record { rFree-𝑎 = rFree-𝑎 ; rFree-f = rFree-f ; rFree-m = rFree-m } = dfree (λ x → toFree (rFree-f x)) rFree-m
  -}
{-
  mutual
    record S-Free {𝑨 𝑩} (F : ∀ {𝑎} → Set 𝑎 → Set 𝑩) (A : Set 𝑨) : Set (sucₗ (𝑨 ⊔ₗ 𝑩)) where
      inductive
      open R-Type
      field
        type : Type
        sPure : type ≡ isPure → Pure A
        rFree : type ≡ isFree → S-Free-Free F A → S-Free F A

    record S-Free-Free {𝑨 𝑩} (F : ∀ {𝑎} → Set 𝑎 → Set 𝑩) (A : Set 𝑨) : Set (sucₗ (𝑨 ⊔ₗ 𝑩)) where
      inductive
      field
        rFree-m : F (S-Free F A)

  mutual
    data D-Free {𝑨 𝑩} (F : ∀ {𝑎} → Set 𝑎 → Set 𝑩) (A : Set 𝑨) : Set (sucₗ (𝑨 ⊔ₗ 𝑩)) where
      dfree : D-Free-Free F A → D-Free F A

    data D-Free-Free {𝑨 𝑩} (F : ∀ {𝑎} → Set 𝑎 → Set 𝑩) (A : Set 𝑨) : Set (sucₗ (𝑨 ⊔ₗ 𝑩)) where
      dfree : F (D-Free F A) → D-Free-Free F A
-}
{-
  mutual
    record Bad-1 : Set where
      inductive
      field
        r : Bad-2 → ⊥

    record Bad-2 : Set where
      inductive
      field
        r : Bad-1
-}
  -- record RFree {𝑨 𝑩} (F : ∀ {𝑎} → Set 𝑎 → Set 𝑩) (A : Set 𝑨) : Set (sucₗ (𝑨 ⊔ₗ 𝑩)) where
  --   inductive
  --   field
  --     isPure : Bool
  --     isFree : Bool
  --     xorPureFree : (isPure ≡ true → isFree ≡ false) × (isPure ≡ false → isFree ≡ true)
  --     purer : isPure ≡ true → A → RFree F A
  --     {freer-𝑎} : isFree ≡ true → Set 𝑨
  --     freer-f : (prf : isFree ≡ true) → freer-𝑎 prf → RFree F A
  --     freer-m : (prf : isFree ≡ true) → F (freer-𝑎 prf)

  -- -- module FreeComparison {α} {A : Set α} ⦃ _ : Eq A ⦄
  -- --   where

  -- --   data _≞_ : Free List A → Free List A → Set (sucₗ α) where
  -- --     Pure : {x : A} → {y : A} → x ≡ y → pure x ≞ pure y
  -- --     Free[] : ∀ {M N : Set α} → (f : M → Free List A) → (g : N → Free List A) → free f [] ≞ free g []
  -- --     Free∷ : ∀ {M N : Set α} → {f : M → Free List A} → {x : M} {xs : List M} → {g : N → Free List A} → {y : N} {ys : List N} →
  -- --             f x ≞ g y →
  -- --             free f xs ≞ free g ys →
  -- --             free f (x ∷ xs) ≞ free g (y ∷ ys)

  -- --   _≞?_ : (flx : Free List A) → (fly : Free List A) → Dec (flx ≞ fly)
  -- --   pure x ≞? pure y with x ≟ y
  -- --   ... | yes x≡y rewrite x≡y = yes (Pure refl)
  -- --   ... | no x≢y = no (λ { (Pure x≡y) → x≢y x≡y })
  -- --   pure _ ≞? free _ _ = no (λ ())
  -- --   free _ _ ≞? pure _ = no (λ ())
  -- --   free fx [] ≞? free fy [] = yes (Free[] fx fy)
  -- --   free fx [] ≞? free fy (y ∷ ys) = no (λ ())
  -- --   free fx (x ∷ xs) ≞? free fy [] = no (λ ())
  -- --   free fx (x ∷ xs) ≞? free fy (y ∷ ys) with fx x ≞? fy y
  -- --   free fx (x ∷ xs) ≞? free fy (y ∷ ys) | yes fxx≞fyy with free fx xs ≞? free fy ys
  -- --   free fx (x ∷ xs) ≞? free fy (y ∷ ys) | yes fxx≞fyy | yes freefxxs≞freefyys = yes (Free∷ fxx≞fyy freefxxs≞freefyys)
  -- --   free fx (x ∷ xs) ≞? free fy (y ∷ ys) | yes fxx≞fyy | no freefxxs≞freefyys = no (λ { (Free∷ x₁ x₂) → freefxxs≞freefyys x₂ })
  -- --   free fx (x ∷ xs) ≞? free fy (y ∷ ys) | no fxx≞fyy = no (λ { (Free∷ x₁ x₂) → fxx≞fyy x₁ })

  -- --   postulate
  -- --     : A → Bool

  -- --   data ⟦_/_⋐_⟧ : (X : Free List A) (isVariable : A → Bool) (Y : Free List B) → Set (sucₗ α) where
  -- --     PurePure : (x y : A) → pure x ⋐ pure y
  -- --     PureFree : (x : A) → ∀ {N : Set α} → (g : N → Free List A) → (ns : List N) → pure x ⋐ free g ns
  -- --     FreeFree : {M N : Set α} →
  -- --                {f : M → Free List A} →
  -- --                {m : M} {ms : List M} →
  -- --                {g : N → Free List A} →
  -- --                {n : N} {ns : List N} →
  -- --                ¬ free f (m ∷ ms) ≞ free g (n ∷ ns) →
  -- --                f m ⋐ g n →
  -- --                free f ms ⋐ free g ns →
  -- --                free f (m ∷ ms) ⋐ free g (n ∷ ns)

  -- --   data _⋐_ : (X : Free List A) (Y : Free List A) → Set (sucₗ α) where
  -- --     PurePure : (x y : A) → pure x ⋐ pure y
  -- --     PureFree : (x : A) → ∀ {N : Set α} → (g : N → Free List A) → (ns : List N) → pure x ⋐ free g ns
  -- --     FreeFree : {M N : Set α} →
  -- --                {f : M → Free List A} →
  -- --                {m : M} {ms : List M} →
  -- --                {g : N → Free List A} →
  -- --                {n : N} {ns : List N} →
  -- --                ¬ free f (m ∷ ms) ≞ free g (n ∷ ns) →
  -- --                f m ⋐ g n →
  -- --                free f ms ⋐ free g ns →
  -- --                free f (m ∷ ms) ⋐ free g (n ∷ ns)

  -- --   _⋐?_ : (X : Free List A) (Y : Free List A) → Dec (X ⋐ Y)
  -- --   _⋐?_ = ?

  -- --   -- data _⋐_ : (X : Free List A) (Y : Free List A) → Set (sucₗ α) where
  -- --   --   Equal : ∀ {X : Free List A} {Y : Free List A} (X≞Y : X ≞ Y) → X ⋐ Y
  -- --   --   PureFree : (x : A) → ∀ {N : Set α} → (g : N → Free List A) → (ns : List N) → pure x ⋐ free g ns
  -- --   --   FreeFree : {M N : Set α} →
  -- --   --              {f : M → Free List A} →
  -- --   --              {m : M} {ms : List M} →
  -- --   --              {g : N → Free List A} →
  -- --   --              {n : N} {ns : List N} →
  -- --   --              ¬ free f (m ∷ ms) ≞ free g (n ∷ ns) →
  -- --   --              f m ⋐ g n →
  -- --   --              free f ms ⋐ free g ns →
  -- --   --              free f (m ∷ ms) ⋐ free g (n ∷ ns)
