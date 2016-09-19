module Sublis&Match where
  open import Postlude

  data Free {𝑨} (F : Set 𝑨 → Set 𝑨) (A : Set 𝑨) : Set (sucₗ 𝑨) where
    pure : A → Free F A
    free : ∀ {𝑎 : Set 𝑨} → (𝑎 → Free F A) → F 𝑎 → Free F A
{-
  record Natlike : Set where
    inductive
    field
      Zero : Natlike
      Suc : Natlike → Natlike
-}{-
  record Freelike {𝑨} (F : Set 𝑨 → Set 𝑨) (A : Set 𝑨) : Set (sucₗ 𝑨) where
    inductive
    field
      make-singleton : A → Freelike F A
      make-tree : ∀ {𝑎 : Set 𝑨} → (𝑎 → Freelike F A) → F 𝑎 → Freelike F A
-}
