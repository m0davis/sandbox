module Free where
  open import Postlude

  data Free {𝑨 𝑩} (F : Set 𝑨 → Set 𝑩) (A : Set 𝑨) : Set (sucₗ (𝑨 ⊔ₗ 𝑩)) where
    pure : A → Free F A
    free : ∀ {𝑎 : Set 𝑨} → (𝑎 → Free F A) → F 𝑎 → Free F A

  -- module FreeComparison {α} {A : Set α} ⦃ _ : Eq A ⦄
  --   where

  --   data _≞_ : Free List A → Free List A → Set (sucₗ α) where
  --     Pure : {x : A} → {y : A} → x ≡ y → pure x ≞ pure y
  --     Free[] : ∀ {M N : Set α} → (f : M → Free List A) → (g : N → Free List A) → free f [] ≞ free g []
  --     Free∷ : ∀ {M N : Set α} → {f : M → Free List A} → {x : M} {xs : List M} → {g : N → Free List A} → {y : N} {ys : List N} →
  --             f x ≞ g y →
  --             free f xs ≞ free g ys →
  --             free f (x ∷ xs) ≞ free g (y ∷ ys)

  --   _≞?_ : (flx : Free List A) → (fly : Free List A) → Dec (flx ≞ fly)
  --   pure x ≞? pure y with x ≟ y
  --   ... | yes x≡y rewrite x≡y = yes (Pure refl)
  --   ... | no x≢y = no (λ { (Pure x≡y) → x≢y x≡y })
  --   pure _ ≞? free _ _ = no (λ ())
  --   free _ _ ≞? pure _ = no (λ ())
  --   free fx [] ≞? free fy [] = yes (Free[] fx fy)
  --   free fx [] ≞? free fy (y ∷ ys) = no (λ ())
  --   free fx (x ∷ xs) ≞? free fy [] = no (λ ())
  --   free fx (x ∷ xs) ≞? free fy (y ∷ ys) with fx x ≞? fy y
  --   free fx (x ∷ xs) ≞? free fy (y ∷ ys) | yes fxx≞fyy with free fx xs ≞? free fy ys
  --   free fx (x ∷ xs) ≞? free fy (y ∷ ys) | yes fxx≞fyy | yes freefxxs≞freefyys = yes (Free∷ fxx≞fyy freefxxs≞freefyys)
  --   free fx (x ∷ xs) ≞? free fy (y ∷ ys) | yes fxx≞fyy | no freefxxs≞freefyys = no (λ { (Free∷ x₁ x₂) → freefxxs≞freefyys x₂ })
  --   free fx (x ∷ xs) ≞? free fy (y ∷ ys) | no fxx≞fyy = no (λ { (Free∷ x₁ x₂) → fxx≞fyy x₁ })

  --   postulate
  --     : A → Bool

  --   data ⟦_/_⋐_⟧ : (X : Free List A) (isVariable : A → Bool) (Y : Free List B) → Set (sucₗ α) where
  --     PurePure : (x y : A) → pure x ⋐ pure y
  --     PureFree : (x : A) → ∀ {N : Set α} → (g : N → Free List A) → (ns : List N) → pure x ⋐ free g ns
  --     FreeFree : {M N : Set α} →
  --                {f : M → Free List A} →
  --                {m : M} {ms : List M} →
  --                {g : N → Free List A} →
  --                {n : N} {ns : List N} →
  --                ¬ free f (m ∷ ms) ≞ free g (n ∷ ns) →
  --                f m ⋐ g n →
  --                free f ms ⋐ free g ns →
  --                free f (m ∷ ms) ⋐ free g (n ∷ ns)

  --   data _⋐_ : (X : Free List A) (Y : Free List A) → Set (sucₗ α) where
  --     PurePure : (x y : A) → pure x ⋐ pure y
  --     PureFree : (x : A) → ∀ {N : Set α} → (g : N → Free List A) → (ns : List N) → pure x ⋐ free g ns
  --     FreeFree : {M N : Set α} →
  --                {f : M → Free List A} →
  --                {m : M} {ms : List M} →
  --                {g : N → Free List A} →
  --                {n : N} {ns : List N} →
  --                ¬ free f (m ∷ ms) ≞ free g (n ∷ ns) →
  --                f m ⋐ g n →
  --                free f ms ⋐ free g ns →
  --                free f (m ∷ ms) ⋐ free g (n ∷ ns)

  --   _⋐?_ : (X : Free List A) (Y : Free List A) → Dec (X ⋐ Y)
  --   _⋐?_ = ?

  --   -- data _⋐_ : (X : Free List A) (Y : Free List A) → Set (sucₗ α) where
  --   --   Equal : ∀ {X : Free List A} {Y : Free List A} (X≞Y : X ≞ Y) → X ⋐ Y
  --   --   PureFree : (x : A) → ∀ {N : Set α} → (g : N → Free List A) → (ns : List N) → pure x ⋐ free g ns
  --   --   FreeFree : {M N : Set α} →
  --   --              {f : M → Free List A} →
  --   --              {m : M} {ms : List M} →
  --   --              {g : N → Free List A} →
  --   --              {n : N} {ns : List N} →
  --   --              ¬ free f (m ∷ ms) ≞ free g (n ∷ ns) →
  --   --              f m ⋐ g n →
  --   --              free f ms ⋐ free g ns →
  --   --              free f (m ∷ ms) ⋐ free g (n ∷ ns)
