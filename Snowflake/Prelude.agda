--{-# OPTIONS --show-implicit #-}
module Snowflake.Prelude where

data ⊥ : Set where

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()
{-# INLINE ⊥-elim #-}

infix 3 ¬_
¬_ : ∀ {a} (A : Set a) → Set a
¬ A = A → ⊥

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

open import Prelude.Memoization
open import Prelude.Nat
open import Prelude.Product

record Valueable {a} (A : Set a) : Set a where
  field
    value : (x : A) → Mem x

open Valueable ⦃ ... ⦄

infixr 0 _$_
_$_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $ x = f x

infixl 0 $-syntax
$-syntax : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
$-syntax = _$_

infixr 0 _!$_
_!$_ : ∀ {a} {A : Set a} {b} {B : A → Set b} → ((x : A) → B x) → ⦃ _ : Valueable A ⦄ → ∀ x → B x
f  !$ x with value x
... | (x' , x-refl) rewrite sym x-refl = f x'

infixl 0 !$-syntax₁
!$-syntax₁ : ∀ {a} {A : Set a} {b} {B : A → Set b} → ((x : A) → B x) → ⦃ _ : Valueable A ⦄ → (x : A) → B x
!$-syntax₁ = _!$_

infixl 0 !$-syntax₂
!$-syntax₂ : ∀ {a} {A : Set a} {b} {B : A → Set b} → ((x : A) → B x) → ⦃ _ : Valueable A ⦄ → (x : A) → B x
!$-syntax₂ = _!$_

syntax $-syntax f x = x |⋙ f
syntax !$-syntax₁ f x = x !|⋙ f
syntax !$-syntax₂ (λ v → f) x = !let v != x !in f

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

infixr 9 _!∘_
_!∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
         (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
         ⦃ _ : Valueable A ⦄ →
         ⦃ _ : {x : A} → Valueable (B x) ⦄ →
         ∀ x → C x (g x)
(f !∘ g) x with value x
... | (x' , x-refl) rewrite sym x-refl with value (g x')
... | (gx' , gx-refl) rewrite sym gx-refl = f !$ gx'
  --!let gx != (g !$ x) !in (f !$ gx)

infixl 9 !∘-syntax
!∘-syntax : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
              (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
              ⦃ _ : Valueable A ⦄ →
              ⦃ _ : {x : A} → Valueable (B x) ⦄ →
              ∀ x → C x (g x)
!∘-syntax = _!∘_

syntax ∘-syntax f g = g ⋙ f
syntax !∘-syntax f g = g !⋙ f

data 𝕃 {𝑨} (𝐴 : Set 𝑨) : Set 𝑨
data _∉_ {𝑨} {𝐴 : Set 𝑨} (x : 𝐴) : 𝕃 𝐴 → Set 𝑨

data 𝕃 {𝑨} (𝐴 : Set 𝑨) where
  ∅ : 𝕃 𝐴
  ✓ : {x₀ : 𝐴} → {x₁s : 𝕃 𝐴} → x₀ ∉ x₁s → 𝕃 𝐴

data _∉_ {𝑨} {𝐴 : Set 𝑨} (𝔞 : 𝐴) where
  ∅ : 𝔞 ∉ ∅
  ● : ∀ {x₀} → 𝔞 ≢ x₀ → ∀ {x₁s} → 𝔞 ∉ x₁s → (x₀∉x₁s : x₀ ∉ x₁s) → 𝔞 ∉ ✓ x₀∉x₁s

mutual
  𝕃μ : ∀ {𝑨} {𝐴 : Set 𝑨} → (l : 𝕃 𝐴) → Mem l
  𝕃μ ∅ = putμ refl
  𝕃μ (✓ x) with ∉μ x
  ... | (mx , x-refl) rewrite sym x-refl = ✓ mx , refl

  ∉μ : ∀ {𝑨} {𝐴 : Set 𝑨} {x : 𝐴} → {l : 𝕃 𝐴} → (x∉l : x ∉ l) → Mem x∉l
  ∉μ ∅ = putμ refl
  ∉μ (● x₂ x₃ x₁) with ∉μ x₃ | ∉μ x₁
  ... | (mx₃ , x₃-refl) | (mx₁ , x₁-refl) rewrite sym x₃-refl | sym x₁-refl = ● x₂ mx₃ mx₁ , refl

instance
  Applyable𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} → Valueable (𝕃 𝐴)
  Applyable𝕃 = record { value = 𝕃μ }

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

open import Prelude.Function using (id {-syntax ofType-})

[a]
 [ab]
 [ba]
 [abc]
 [cab]
 [cba]
 [abcd]
 [dcab]
 [dcba] : 𝕃 T -- TODO why is indentation needed?

[a]    = ✓ a∅
[ab]   = ✓ a∉b
[ba]   = ✓ b∉a
[abc]  = ✓ a∉bc
[cab]  = ✓ c∉ab
[cba]  = ✓ c∉ba
[abcd] = ✓ a∉bcd
[dcab] = ✓ d∉cab
[dcba] = ✓ d∉cba

last : ∀ {𝑨} {𝐴 : Set 𝑨} {L} → ∅⊂ L → 𝐴
last [ x₀ ] = x₀
last (tail= (✓ x₁∉x₂s)) = last (✓ x₁∉x₂s)

_[lastIndex]=last : ∀ {𝑨} {𝐴 : Set 𝑨} {L : 𝕃 𝐴} → (∅⊂L : ∅⊂ L) → L [ lastIndex ∅⊂L ]= last ∅⊂L
[ _ ] [lastIndex]=last = here ∅
(✓ (x₀∉x₁s₁ ↶ x ↷ x₀∉x₁s)) [lastIndex]=last = there (x₀∉x₁s₁ ↶ x ↷ x₀∉x₁s) (✓ x₀∉x₁s [lastIndex]=last)

mutual
  init : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀s : 𝕃 𝐴} (∅⊂x₀s : ∅⊂ x₀s) → 𝕃 𝐴
  init [ _ ] = ∅
  init (✓ (x₀∉x₂s ↶ _ ↷ x₁∉x₂s)) = ✓ (init∉ (✓ _) (x₀∉x₂s ↶ _ ↷ x₁∉x₂s))

  init∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀ : 𝐴} {x₁s : 𝕃 𝐴} (∅⊂x₁s : ∅⊂ x₁s) → x₀ ∉ x₁s → x₀ ∉ init ∅⊂x₁s
  init∉ () ∅
  init∉ (✓ _) (∅ ↶ _ ↷ ∅) = ∅
  init∉ (✓ _) ((x₀∉x₃s ↶ x₀≢x₂ ↷ x₂∉x₃s) ↶ x₀≢x₁ ↷ (x₁∉x₃s ↶ x₁≢x₂ ↷ .x₂∉x₃s)) = init∉ _ (x₀∉x₃s ↶ x₀≢x₂ ↷ x₂∉x₃s) ↶ x₀≢x₁ ↷ init∉ _ (x₁∉x₃s ↶ x₁≢x₂ ↷ x₂∉x₃s)

rotateDown∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {xs : 𝕃 𝐴} (∅⊂xs : ∅⊂ xs) → last ∅⊂xs ∉ init ∅⊂xs
rotateDown∉ [ _ ] = ∅
rotateDown∉ (✓ (x₀∉x₂s ↶ x₀≢x₁ ↷ x₁∉x₂s)) =
  let xₙ≢x₀ = λ lastx₁s≡x₀ → let x₁s[last]=x₀ : ✓ x₁∉x₂s [ lastIndex (✓ x₁∉x₂s) ]= _
                                 x₁s[last]=x₀ = subst (✓ x₁∉x₂s [ lastIndex (✓ x₁∉x₂s) ]=_) lastx₁s≡x₀ (✓ x₁∉x₂s [lastIndex]=last)
                             in
                               ⊥-𝕃[i]=x∉𝕃 x₁s[last]=x₀ (x₀∉x₂s ↶ x₀≢x₁ ↷ x₁∉x₂s)
  in
    rotateDown∉ (✓ x₁∉x₂s) ↶ xₙ≢x₀ ↷ init∉ (✓ x₁∉x₂s) (x₀∉x₂s ↶ x₀≢x₁ ↷ x₁∉x₂s)

-- rotateDown "A12345678Z" = "ZA12345678"
rotateDown : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → 𝕃 𝐴
rotateDown ∅ = ∅
rotateDown [ x₀ ] = [ x₀ ]
rotateDown (✓ x₀∉x₁s) = ✓ (rotateDown∉ (✓ x₀∉x₁s))

rotateDown-ex : 𝕃→𝑳 (rotateDown [abcd]) ≡ (⋆d ∷ₗ ⋆a ∷ₗ ⋆b ∷ₗ ⋆c ∷ₗ ∅)
rotateDown-ex = refl

-- swapTop "AB23456789" = "BA23456789"
swapTop : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → 𝕃 𝐴
swapTop ∅ = ∅
swapTop [ x₀ ] = [ x₀ ]
swapTop (✓ (x₀∉x₂s ↶ x₀≢x₁ ↷ x₁∉x₂s)) = ✓ (x₁∉x₂s ↶ sym≢ x₀≢x₁ ↷ x₀∉x₂s)

swapTop-ex : 𝕃→𝑳 (swapTop [abcd]) ≡ (⋆b ∷ₗ ⋆a ∷ₗ ⋆c ∷ₗ ⋆d ∷ₗ ∅)
swapTop-ex = refl

-- rotateDownBy 2 "01234567AB" = "AB01234567"
-- rotateDownBy 3 s = rotateDown (rotateDown (rotateDown s))
open import Agda.Builtin.Nat using (_<_)
open import Agda.Builtin.Bool

{-# TERMINATING #-}
rotateDownBy : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
rotateDownBy n ∅ = ∅
rotateDownBy 0 x = x
rotateDownBy (suc n) x with length x < suc (suc n)
... | true = rotateDownBy (suc n - length x) x
... | false = x !|⋙ rotateDown !⋙ rotateDownBy n

rotateDownBy-ex : 𝕃→𝑳 (rotateDownBy 46 [abcd]) ≡ (⋆c ∷ₗ ⋆d ∷ₗ ⋆a ∷ₗ ⋆b ∷ₗ ∅)
rotateDownBy-ex = refl

-- raiseFromBottom 3 "012345X789" = "01234X5789"
-- i.e. take the 3rd (indexed-from-the-right) item (X) and move it one space to the left
-- raiseFromBottom (lastIndex s - 1) s = swapTop s
raiseFromBottom : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
raiseFromBottom _ ∅ = ∅
raiseFromBottom _ [ x₀ ] = [ x₀ ]
raiseFromBottom n xs = xs !|⋙ rotateDownBy (2 + n) !⋙ swapTop !⋙ rotateDownBy (length xs - 2 - n)

raiseFromBottom-ex : 𝕃→𝑳 (raiseFromBottom 2 [abcd]) ≡ (⋆b ∷ₗ ⋆a ∷ₗ ⋆c ∷ₗ ⋆d ∷ₗ ∅)
raiseFromBottom-ex = refl

-- raiseBottomBy 2 "012345678X" = "0123456X78"
-- i.e. take the last item (X) and move it 2 spaces to the left
raiseBottomBy : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
raiseBottomBy _ ∅ = ∅
raiseBottomBy _ [ x₀ ] = [ x₀ ]
raiseBottomBy 0 xs = xs
raiseBottomBy (suc n) xs = xs !|⋙ raiseBottomBy n !⋙ raiseFromBottom n

raiseBottomBy-ex : 𝕃→𝑳 (raiseBottomBy 2 [abcd]) ≡ (⋆a ∷ₗ ⋆d ∷ₗ ⋆b ∷ₗ ⋆c ∷ₗ ∅)
raiseBottomBy-ex = refl

-- ⟦ 2 ⋆← 6 ⟧ "012345X789"
-- raiseFromTopBy 6 2 "012345X789" = "0123X45789"
-- i.e. take the 6th (indexed-from-the-left) item (X) and move it 2 places to the left
-- raiseFromTopBy 1 1 = swapTop
raiseFromTopBy : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → ℕ → 𝕃 𝐴 → 𝕃 𝐴
raiseFromTopBy _ 0 xs = xs
raiseFromTopBy n m xs with length xs
... | l with suc n ≟ l
... | yes _ = xs !|⋙ raiseBottomBy m
... | no _  = xs !|⋙ rotateDownBy (l - (suc n)) !⋙ raiseBottomBy m !⋙ rotateDownBy (suc n)

raiseFromTopBy-ex : 𝕃→𝑳 (raiseFromTopBy 2 2 [abcd]) ≡ (⋆c ∷ₗ ⋆a ∷ₗ ⋆b ∷ₗ ⋆d ∷ₗ ∅)
raiseFromTopBy-ex = refl

reorder : ∀ {𝑨} {𝐴 : Set 𝑨} (L : 𝕃 𝐴) → 𝑳 ℕ → 𝕃 𝐴
reorder xs perm = go 0 perm xs where
  go : ∀ {𝑨} {𝐴 : Set 𝑨} → (n : ℕ) → 𝑳 ℕ → (L : 𝕃 𝐴) → 𝕃 𝐴
  go _ _ ∅ = ∅
  go _ ∅ xs = xs
  go n (p₀ ∷ₗ ps) xs = go (suc n) ps !$ raiseFromTopBy (n + p₀) p₀ xs

-- module M₁ where
--   data Fin : ℕ → Set where
--     zero : Fin 0
--     suc : ∀ {n} → Fin n → Fin (suc n)

--   data PermutationList : ℕ → Set where
--     ∅ : PermutationList 0
--     _∷_ : ∀ {n} → Fin n → PermutationList n → PermutationList (suc n)
--   {-
--   invariantLength-init : ∀ {𝑨} {𝐴 : Set 𝑨} (x₀ : 𝐴) (x₁s : 𝕃 𝐴) (x₀∉x₁s
--     init : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀s : 𝕃 𝐴} (∅⊂x₀s : ∅⊂ x₀s) → 𝕃 𝐴
--   -}

--   invariantLength-rotateDown : ∀ {𝑨} {𝐴 : Set 𝑨} (xs : 𝕃 𝐴) → length (rotateDown xs) ≡ length xs
--   invariantLength-rotateDown {𝑨} {𝐴} ∅ = {!!}
--   invariantLength-rotateDown {𝑨} {𝐴} (✓ {x₀ = x₀} {x₁s = x₁s} x₀∉x₁s) = {!!}
--   {-
--   invariantLength-rotateDown : ∀ {𝑨} {𝐴 : Set 𝑨} (xs : 𝕃 𝐴) → length (rotateDown xs) ≡ length xs
--   invariantLength-rotateDown ∅ = refl
--   invariantLength-rotateDown [ x₀ ] = refl
--   invariantLength-rotateDown (x₀ ₀∷₁ x₁ ∷⟦ x₂s ⟧) = {!!}
--   -}

--   {-# TERMINATING #-}
--   rotateDownBy' : ∀ {𝑨} {𝐴 : Set 𝑨} → (xs : 𝕃 𝐴) → Fin (length xs) → 𝕃 𝐴
--   rotateDownBy' ∅ zero = ∅
--   rotateDownBy' (✓ {x₀ = x₀} {x₁s = x₁s} x₀∉x₁s) (suc {n = n} n') = rotateDownBy' (rotateDown (✓ x₀∉x₁s)) (subst Fin (sym {!!}) n') -- (subst Fin (sym {!invariantLength-rotateDown!}) n) -- (subst {!!} (sym {!!}) {!!})

--   --rotateDownBy' n ∅ = ∅
--   --rotateDownBy' x zero = x
--   --rotateDownBy' x (suc n) = x |⋙ rotateDown ⋙ rotateDownBy' n

-- module M₂ where
--   data Fin : ℕ → Set where
--     zero : ∀ ..{n} → Fin (suc n)
--     suc  : ∀ ..{n} (i : Fin n) → Fin (suc n)

--   postulate
--     invariantLength : ∀ {𝑨} {𝐴 : Set 𝑨} (x₀ : 𝐴) (x₁s : 𝕃 𝐴) (x₀∉x₁s : x₀ ∉ x₁s) → suc (length x₁s) ≡ length (rotateDown (✓ {x₀ = x₀} {x₁s = x₁s} x₀∉x₁s))
--     expandFin : ∀ {n} → Fin n → Fin (suc n)

--   {-# TERMINATING #-}
--   rotateDownBy' : ∀ {𝑨} {𝐴 : Set 𝑨} → (xs : 𝕃 𝐴) → Fin (suc (length xs)) → 𝕃 𝐴
--   rotateDownBy' ∅ zero = ∅
--   rotateDownBy' ∅ (suc ())
--   rotateDownBy' (✓ x₀∉x₁s) zero = ✓ x₀∉x₁s
--   rotateDownBy' (✓ {x₀ = x₀} {x₁s = x₁s} x₀∉x₁s) (suc n) = rotateDownBy' (rotateDown (✓ {x₀ = x₀} {x₁s = x₁s} x₀∉x₁s)) (expandFin (subst Fin (invariantLength x₀ x₁s x₀∉x₁s) n))


-- module M₃ where
--   open import Prelude.Nat
--   open import Prelude.Bool
--   open import Prelude.Equality

--   invariantLength₁ : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀ : 𝐴} {x₁s} {x₀∉x₁s : x₀ ∉ x₁s} → length x₁s ≡ length (init (✓ x₀∉x₁s))
--   invariantLength₁ {𝑨} {𝐴} {x₀} {.∅} {∅} = refl
--   invariantLength₁ {𝑨} {𝐴} {x₁} {.(✓ {_} {_} {x₀} {x₁s} x₀∉x₁s)} {● {x₀ = x₀} x {x₁s = x₁s} x₀∉x₁s₁ x₀∉x₁s} = cong suc (invariantLength₁ {x₁s = x₁s})

--   invariantLength₂ : ∀ {𝑨} {𝐴 : Set 𝑨} {xs : 𝕃 𝐴} → length xs ≡ length (rotateDown xs)
--   invariantLength₂ {xs = ∅} = refl
--   invariantLength₂ {xs = ✓ ∅} = refl
--   invariantLength₂ {xs = ✓ {x₀ = x₀} {x₁s = x₁s} (● {x₀ = x₁} x₀≢x₁ {x₁s = x₂s} x₀∉x₂s x₁∉x₂s)} = cong (λ x → suc (suc x)) (invariantLength₁ {x₀∉x₁s = x₁∉x₂s})

--   thm₁ : ∀ {n m} → IsTrue (lessNat (suc n) m) → IsTrue (lessNat n m)
--   thm₁ {n} {zero} ()
--   thm₁ {zero} {suc zero} ()
--   thm₁ {zero} {suc (suc m)} true = true
--   thm₁ {suc n} {suc m} x = thm₁ {n = n} {m = m} x

--   thm₂ : ∀ {n m} → IsTrue (lessNat (suc n) m) → IsTrue (lessNat n m)
--   thm₂ {zero} {zero} ()
--   thm₂ {zero} {suc _} _ = true
--   thm₂ {suc n} {zero} ()
--   thm₂ {suc n} {suc m} x = thm₂ {n = n} {m = m} x

--   rotateDownBy' : ∀ {𝑨} {𝐴 : Set 𝑨} {n : ℕ} → (xs : 𝕃 𝐴) (n<xs : IsTrue (n < length xs)) → 𝕃 𝐴
--   rotateDownBy' {𝑨} {𝐴} {zero} xs _ = xs
--   rotateDownBy' {𝑨} {𝐴} {suc n} xs n<xs = rotateDownBy' {n = n} (rotateDown xs) (thm₂ {n = n} {m = length (rotateDown xs)} (subst (λ x → IsTrue (lessNat (suc n) x)) (invariantLength₂ {xs = xs}) n<xs))

-- open import Prelude.Fin
-- open import Data.Fin
