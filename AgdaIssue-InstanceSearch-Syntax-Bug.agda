open import Prelude.Empty

open import Agda.Primitive
open import Agda.Builtin.Nat
     using ( zero
           ; suc
           ; _-_
           ; _+_
           )
  renaming (Nat to ℕ)
open import Agda.Builtin.Equality
     using (_≡_; refl)
open import Agda.Builtin.List
     using ()
  renaming (List to 𝑳
           ;[] to ∅
           ; _∷_ to _∷ₗ_
           )

data Dec {a} (P : Set a) : Set a where
  yes : P → Dec P
  no  : ¬ P → Dec P

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

REL : ∀ {a b} → Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
REL A B ℓ = A → B → Set ℓ

Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
Rel A ℓ = REL A A ℓ

_Respects_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → (A → Set ℓ₁) → Rel A ℓ₂ → Set _
P Respects _∼_ = ∀ {x y} → x ∼ y → P x → P y

Substitutive : ∀ {a ℓ₁} {A : Set a} → Rel A ℓ₁ → (ℓ₂ : Level) → Set _
Substitutive {A = A} _∼_ p = (P : A → Set p) → P Respects _∼_

subst : ∀ {a p} {A : Set a} → Substitutive (_≡_ {A = A}) p
subst P refl p = p

sucsuc≡ : ∀ {a b : ℕ} → suc a ≡ suc b → a ≡ b
sucsuc≡ refl = refl

_≟_ : (a : ℕ) → (b : ℕ) → Dec (a ≡ b)
zero ≟ zero = yes refl
zero ≟ suc b = no (λ ())
suc a ≟ zero = no (λ ())
suc a ≟ suc b with a ≟ b
… | yes eq rewrite eq = yes refl
… | no neq = no (λ x → ⊥-elim (neq (sucsuc≡ x)))

_≢_ : ∀ {a} {A : Set a} → A → A → Set a
A ≢ B = ¬ A ≡ B

data 𝕃 {𝑨} (𝐴 : Set 𝑨) : Set 𝑨
data _∉_ {𝑨} {𝐴 : Set 𝑨} (x : 𝐴) : 𝕃 𝐴 → Set 𝑨

data 𝕃 {𝑨} (𝐴 : Set 𝑨) where
  ∅ : 𝕃 𝐴
  ✓ : {x₀ : 𝐴} → {x₁s : 𝕃 𝐴} → x₀ ∉ x₁s → 𝕃 𝐴

data _∉_ {𝑨} {𝐴 : Set 𝑨} (𝔞 : 𝐴) where
  ∉∅ : 𝔞 ∉ ∅
  ∉∷ : ∀ {x₀} → 𝔞 ≢ x₀ → ∀ {x₁s} → 𝔞 ∉ x₁s → (x₀∉x₁s : x₀ ∉ x₁s) → 𝔞 ∉ ✓ x₀∉x₁s

--pattern ⟦_⟧ x₀∉x₁s = ✓ x₀∉x₁s                                      -- ⟦ x₀∉x₁s ⟧
pattern tail= x₁s = ✓ {x₁s = x₁s} _                                -- tail= x₁s
pattern [_] x₀ = ✓ {x₀ = x₀} ∉∅                                    -- [ x₀ ]
pattern _₀∷₁_∷⟦_⟧ x₀ x₁ x₂s = ✓ {x₀ = x₀} (∉∷ {x₁} _ {x₂s} _ _)    -- x₀ ₀∷₁ x₁ ∷⟦ x₂s ⟧

{-
read
∅⊂∷ {x₀} {∅} _
∅⊂∷ {x₁s = ✓ x₁∉x₂s} _
✓ (∉∷ x₀≢x₁ x₀∉x₂s x₁∉x₂s)
∅⊂∷ ∉∅
∅⊂∷ (∉∷ x x₀∉x₁s₁ x₀∉x₁s)
∅⊂∷ (∉∷ _ x₀∉x₂s x₁∉x₂s)
∉∅
∉∷ _ ∉∅ ∉∅
∉∷ x₀≢x₁ (∉∷ x₀≢x₂ x₀∉x₃s x₂∉x₃s) (∉∷ x₁≢x₂ x₁∉x₃s .x₂∉x₃s)

∅⊂∷ {x₀} (∉∷ {x₁} x₀≢x₁ {x₂s} x₀∉x₂s x₁∉x₂s)

write
∅⊂∷ _
∉∷ _ x₀∉x₂s x₁∉x₂s
✓ x₁∉x₂s [ lastIndex (∅⊂∷ x₁∉x₂s) ]= x₀
✓ x₁∉x₂s [ lastIndex (∅⊂∷ x₁∉x₂s) ]=_
✓ (rotate∉ (∅⊂∷ x₀∉x₁s))
✓ (∉∷ (sym' x₀≢x₁) x₁∉x₂s x₀∉x₂s)
✓ (init∉ (∅⊂∷ _) (∉∷ _ x₀∉x₂s x₁∉x₂s))
∉∷ a≢b ∉∅ ∉∅
∉∷ a≢b a∉c b∉c
here ∉∅
there (∉∷ x x₀∉x₁s₁ x₀∉x₁s) (last-thm₁ (∅⊂∷ x₀∉x₁s))
∉∷ x₀≢x₁ (init∉ _ (∉∷ x₀≢x₂ x₀∉x₃s x₂∉x₃s)) (init∉ _ (∉∷ x₁≢x₂ x₁∉x₃s x₂∉x₃s))

-}

𝕃→𝑳 : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → 𝑳 𝐴
𝕃→𝑳 ∅ = ∅
𝕃→𝑳 [ x ] = x ∷ₗ ∅
𝕃→𝑳 (x₀ ₀∷₁ x₁ ∷⟦ x₂s ⟧) = x₀ ∷ₗ x₁ ∷ₗ 𝕃→𝑳 x₂s

data _∈_ {𝑨} {𝐴 : Set 𝑨} (𝔞 : 𝐴) : 𝕃 𝐴 → Set 𝑨 where
  here : ∀ {x₀s} (𝔞∉x₀s : 𝔞 ∉ x₀s) → 𝔞 ∈ ✓ 𝔞∉x₀s
  there : ∀ {x₁s} → (𝔞∈x₁s : 𝔞 ∈ x₁s) → ∀ {x₀} → (x₀∉x₁s : x₀ ∉ x₁s)  → 𝔞 ∈ ✓ x₀∉x₁s

data _[_]=_ {𝑨} {𝐴 : Set 𝑨} : 𝕃 𝐴 → ℕ → 𝐴 → Set 𝑨 where
  here  : ∀ {𝔞 xs} (𝔞∉xs : 𝔞 ∉ xs) → ✓ 𝔞∉xs [ 0 ]= 𝔞
  there : ∀ {x₀ x₁s} (x₀∉x₁s : x₀ ∉ x₁s) {i 𝔞} (x₁s[i]=𝔞 : x₁s [ i ]= 𝔞) → ✓ x₀∉x₁s [ suc i ]= 𝔞

[]=-thm₀ : ∀ {𝑨} {𝐴 : Set 𝑨} {L : 𝕃 𝐴} {n} {a} → L [ n ]= a → a ∉ L → ⊥
[]=-thm₀ (here 𝔞∉xs) (∉∷ x x₁ .𝔞∉xs) = x refl
[]=-thm₀ (there x₀∉x₁s x) (∉∷ x₁ x₂ .x₀∉x₁s) = []=-thm₀ x x₂

data ∅⊂_ {𝑨} {𝐴 : Set 𝑨} : 𝕃 𝐴 → Set 𝑨 where
  ∅⊂∷ : ∀ {x₀ x₁s} → (x₀∉x₁s : x₀ ∉ x₁s) → ∅⊂ ✓ x₀∉x₁s

lastIndex : ∀ {𝑨} {𝐴 : Set 𝑨} {L : 𝕃 𝐴} (∅⊂L : ∅⊂ L) → ℕ
lastIndex (∅⊂∷ ∉∅) = 0
lastIndex (∅⊂∷ (∉∷ x x₀∉x₁s₁ x₀∉x₁s)) = suc (lastIndex (∅⊂∷ x₀∉x₁s))

length : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → ℕ
length ∅ = 0
length (tail= x₁s) = suc (length x₁s)

sym' : ∀ {𝑨} {𝐴 : Set 𝑨} {x y : 𝐴} → x ≢ y → y ≢ x
sym' x₁ x₂ = x₁ (sym x₂)

postulate
  T : Set
  ⋆a ⋆b ⋆c ⋆d : T
  a≢b : ⋆a ≢ ⋆b
  a≢c : ⋆a ≢ ⋆c
  a≢d : ⋆a ≢ ⋆d
  b≢c : ⋆b ≢ ⋆c
  b≢d : ⋆b ≢ ⋆d
  c≢d : ⋆c ≢ ⋆d

b≢a = sym' a≢b
c≢a = sym' a≢c
d≢a = sym' a≢d
c≢b = sym' b≢c
d≢b = sym' b≢d
d≢c = sym' c≢d

a∉∅ : ⋆a ∉ ∅
a∉∅ = ∉∅

a∉b   = ∉∷ a≢b ∉∅ ∉∅
c∉b   = ∉∷ c≢b ∉∅ ∉∅
d∉b   = ∉∷ d≢b ∉∅ ∉∅
a∉c   = ∉∷ a≢c ∉∅ ∉∅
b∉c   = ∉∷ b≢c ∉∅ ∉∅
c∉d   = ∉∷ c≢d ∉∅ ∉∅
b∉d   = ∉∷ b≢d ∉∅ ∉∅
a∉d   = ∉∷ a≢d ∉∅ ∉∅
b∉a   = ∉∷ b≢a ∉∅ ∉∅
c∉a   = ∉∷ c≢a ∉∅ ∉∅
d∉a   = ∉∷ d≢a ∉∅ ∉∅
a∉bc  = ∉∷ a≢b a∉c b∉c
a∉cd  = ∉∷ a≢c a∉d c∉d
b∉cd  = ∉∷ b≢c b∉d c∉d
c∉ab  = ∉∷ c≢a c∉b a∉b
d∉ab  = ∉∷ d≢a d∉b a∉b
c∉ba  = ∉∷ c≢b c∉a b∉a
d∉ba  = ∉∷ d≢b d∉a b∉a
a∉bcd = ∉∷ a≢b a∉cd b∉cd
d∉cab = ∉∷ d≢c d∉ab c∉ab
d∉cba = ∉∷ d≢c d∉ba c∉ba

[a] = ? ∋ (✓ a∉∅) where
  open import Prelude

  id' : ∀ {a} {A : Set a} → A → A
  id' = id
  {-# INLINE id' #-}

  infixl -10 id'
  syntax id' {A = A} x = A ∋ x

[abcd] = ✓ a∉bcd

-- rotateBy 2 "0123456789" = "8901234567"
-- rotateBy 3 s = rotate (rotate (rotate s))
rotateBy : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
rotateBy 0 x = ?
rotateBy (suc n) x = ?

rotateBy-ex : 𝕃→𝑳 (rotateBy 2 [abcd]) ≡ (⋆c ∷ₗ ⋆d ∷ₗ ⋆a ∷ₗ ⋆b ∷ₗ ∅)
rotateBy-ex = refl
