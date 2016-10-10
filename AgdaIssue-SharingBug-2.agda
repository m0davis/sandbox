
open import Prelude

record Traversable {a} (T : Set a → Set a) : Set (lsuc a) where
  field
    traverse : ∀ {F : Set a → Set a} {A B} {{AppF : Applicative F}} → (A → F B) → T A → F (T B)

open Traversable {{...}} public


-- --open import Prelude
-- open import Agda.Primitive

-- open import

-- -- record Applicative {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
-- --   -- field
-- --     -- pure  : ∀ {A} → A → F A
-- --     -- _<*>_ : ∀ {A B} → F (A → B) → F A → F B

-- -- open Applicative {{...}}

-- -- record Traversable {a} (T : Set a → Set a) : Set (lsuc a) where
-- --   field
-- --     traverse : ∀ {F A B} {{AppF : Applicative F}} → (A → F B) → T A → F (T B)
