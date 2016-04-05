open import Prelude.Empty

infixr 0 _$_
_$_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $ x = f x

infixl 0 $-syntax
$-syntax : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
$-syntax = _$_

syntax $-syntax f x = x |⋙ f

infixr 9 _∘_
_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
        (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
        ∀ x → C x (g x)
(f ∘ g) x = f (g x)
{-# INLINE _∘_ #-}

infixl 9 ∘-syntax
∘-syntax : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
           (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
           ∀ x → C x (g x)
∘-syntax = _∘_

syntax ∘-syntax f g = g ⋙ f

open import Agda.Primitive
open import Agda.Builtin.Nat public
     using ( zero
           ; suc
           ; _-_
           ; _+_
           )
  renaming (Nat to ℕ)
open import Agda.Builtin.Equality public
     using (_≡_; refl)
open import Agda.Builtin.List public
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
  ∅ : 𝔞 ∉ ∅
  ● : ∀ {x₀} → 𝔞 ≢ x₀ → ∀ {x₁s} → 𝔞 ∉ x₁s → (x₀∉x₁s : x₀ ∉ x₁s) → 𝔞 ∉ ✓ x₀∉x₁s

--pattern ⟦_⟧ x₀∉x₁s = ✓ x₀∉x₁s

data ∅⊂_ {𝑨} {𝐴 : Set 𝑨} : 𝕃 𝐴 → Set 𝑨 where
  ✓ : ∀ {x₀ x₁s} → (x₀∉x₁s : x₀ ∉ x₁s) → ∅⊂ ✓ x₀∉x₁s

pattern tail= x₁s = ✓ {x₁s = x₁s} _
pattern [_] x₀ = ✓ {x₀ = x₀} ∅
pattern _₀∷₁_∷⟦_⟧ x₀ x₁ x₂s = ✓ {x₀ = x₀} (● {x₁} _ {x₂s} _ _)

pattern _↶_↷_ x₀∉x₂s x₀≢x₁ x₁∉x₂s = ● x₀≢x₁ x₀∉x₂s x₁∉x₂s

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

⊥-𝕃[i]=x∉𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} {L : 𝕃 𝐴} {n} {a} → L [ n ]= a → a ∉ L → ⊥
⊥-𝕃[i]=x∉𝕃 (here _) (_ ↶ x ↷ _) = x refl
⊥-𝕃[i]=x∉𝕃 (there _ x) (x₂ ↶ _ ↷ _) = ⊥-𝕃[i]=x∉𝕃 x x₂

lastIndex : ∀ {𝑨} {𝐴 : Set 𝑨} {L : 𝕃 𝐴} (∅⊂L : ∅⊂ L) → ℕ
lastIndex [ _ ] = 0
lastIndex (✓ (_ ↶ _ ↷ x₀∉x₁s)) = suc (lastIndex (✓ x₀∉x₁s))

length : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → ℕ
length ∅ = 0
length (tail= x₁s) = suc (length x₁s)

sym≢ : ∀ {𝑨} {𝐴 : Set 𝑨} {x y : 𝐴} → x ≢ y → y ≢ x
sym≢ x₁ x₂ = x₁ (sym x₂)

postulate
  T : Set
  ⋆a ⋆b ⋆c ⋆d : T
  a≢b : ⋆a ≢ ⋆b
  a≢c : ⋆a ≢ ⋆c
  a≢d : ⋆a ≢ ⋆d
  b≢c : ⋆b ≢ ⋆c
  b≢d : ⋆b ≢ ⋆d
  c≢d : ⋆c ≢ ⋆d

b≢a = sym≢ a≢b
c≢a = sym≢ a≢c
d≢a = sym≢ a≢d
c≢b = sym≢ b≢c
d≢b = sym≢ b≢d
d≢c = sym≢ c≢d

a∅ : ⋆a ∉ ∅
a∅ = ∅

{-
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
regexp scratch
=======================================================
\1 ↶ \2 ↷ \3\4
=======================================================
\(?:●\)                    -- function head
\(?: \|$\)+                -- delimiter
\(?2:[^ (){}]+?\)          -- parm x₀≢x₁
\(?: \|$\)+                -- delimiter
\(?1:[^ (){}]+?\)          -- parm x₀∉x₂s
\(?: \|$\)+                -- delimiter
\(?3:[^ (){}]+?\)          -- parm x₁∉x₂s
\(?4:\([ (){}]\|$\|\'\)\)  -- end
=======================================================
\(?:●\)\(?: \|$\)+\(?2:[^ (){}]+?\)\(?: \|$\)+\(?1:[^ (){}]+?\)\(?: \|$\)+\(?3:[^ (){}]+?\)\(?4:\([ (){}]\|$\|\'\)\)
=======================================================
● x₀≢x₁ x₀∉x₂s x₁∉x₂s
<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
-}
----------------------------------------------------------------------------------------------------------------------------------------
a∉b   = ∅ ↶ a≢b ↷ ∅
c∉b   = ∅ ↶ c≢b ↷ ∅
d∉b   = ∅ ↶ d≢b ↷ ∅
a∉c   = ∅ ↶ a≢c ↷ ∅
b∉c   = ∅ ↶ b≢c ↷ ∅
c∉d   = ∅ ↶ c≢d ↷ ∅
b∉d   = ∅ ↶ b≢d ↷ ∅
a∉d   = ∅ ↶ a≢d ↷ ∅
b∉a   = ∅ ↶ b≢a ↷ ∅
c∉a   = ∅ ↶ c≢a ↷ ∅
d∉a   = ∅ ↶ d≢a ↷ ∅
a∉bc  = a∉c ↶ a≢b ↷ b∉c
a∉cd  = a∉d ↶ a≢c ↷ c∉d
b∉cd  = b∉d ↶ b≢c ↷ c∉d
c∉ab  = c∉b ↶ c≢a ↷ a∉b
d∉ab  = d∉b ↶ d≢a ↷ a∉b
c∉ba  = c∉a ↶ c≢b ↷ b∉a
d∉ba  = d∉a ↶ d≢b ↷ b∉a
a∉bcd = a∉cd ↶ a≢b ↷ b∉cd
d∉cab = d∉ab ↶ d≢c ↷ c∉ab
d∉cba = d∉ba ↶ d≢c ↷ c∉ba
