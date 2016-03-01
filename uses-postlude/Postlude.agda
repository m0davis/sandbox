module Postlude where

open import Prelude renaming
  (_==_ to _≟_
  ; Nat to ℕ
  ; lsuc to sucₗ
  ; _⊔_ to _⊔ₗ_
--  ; fst to proj₁
--  ; snd to proj₂
  ; Either to _⊎_
  ; left to inj₁
  ; right to inj₂
  )
  hiding
  (pure
  ; diff
  ; singleton
  ; _,_
  ; Σ
  ; fst
  ; snd
  ; _×_
  ) public



infixr 4 _,_
infixr 2 _×_

------------------------------------------------------------------------
-- Definition

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ₗ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

-- The syntax declaration below is attached to Σ-syntax, to make it
-- easy to import Σ without the special syntax.

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ₗ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ₗ b)
∃ = Σ _

∄ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ₗ b)
∄ P = ¬ ∃ P

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ₗ b)
A × B = Σ[ x ∈ A ] B

_≢_ : ∀ {x} {X : Set x} (A B : X) → Set x
A ≢ B = ¬ (A ≡ B)

contradiction : ∀ {a p} {A : Set a} {P : Set p} → P → ¬ P → A
contradiction p np = ⊥-elim (np p)

REL : ∀ {a b} → Set a → Set b → (ℓ : Level) → Set (a ⊔ₗ b ⊔ₗ sucₗ ℓ)
REL A B ℓ = A → B → Set ℓ

Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ₗ sucₗ ℓ)
Rel A ℓ = REL A A ℓ

_Respects_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → (A → Set ℓ₁) → Rel A ℓ₂ → Set _
P Respects _∼_ = ∀ {x y} → x ∼ y → P x → P y

Substitutive : ∀ {a ℓ₁} {A : Set a} → Rel A ℓ₁ → (ℓ₂ : Level) → Set _
Substitutive {A = A} _∼_ p = (P : A → Set p) → P Respects _∼_

subst : ∀ {a p} {A : Set a} → Substitutive (_≡_ {A = A}) p
subst P refl p = p

⌊_⌋ : ∀ {p} {P : Set p} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

T : Bool → Set
T true  = ⊤
T false = ⊥

True : ∀ {p} {P : Set p} → Dec P → Set
True Q = T ⌊ Q ⌋

toWitness : ∀ {p} {P : Set p} {Q : Dec P} → True Q → P
toWitness {Q = yes p} _  = p
toWitness {Q = no  _} ()
