module Snowflake.Prelude-NoUniverse where

open import Agda.Builtin.Strict

infixr 0 _$!_
_$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $! x = primForce x f

data ⊥ : Set where

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()
{-# INLINE ⊥-elim #-}

infix 3 ¬_
¬_ : ∀ {a} (A : Set a) → Set a
¬ A = A → ⊥

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

data 𝕃 (𝐴 : Set) : Set
data _∉_ {𝐴 : Set} (x : 𝐴) : 𝕃 𝐴 → Set

data 𝕃 (𝐴 : Set) where
  ∅ : 𝕃 𝐴
  ✓ : {x₀ : 𝐴} → {x₁s : 𝕃 𝐴} → x₀ ∉ x₁s → 𝕃 𝐴

data _∉_ {𝐴 : Set} (𝔞 : 𝐴) where
  ∅ : 𝔞 ∉ ∅
  ● : ∀ {x₀} → 𝔞 ≢ x₀ → ∀ {x₁s} → 𝔞 ∉ x₁s → (x₀∉x₁s : x₀ ∉ x₁s) → 𝔞 ∉ ✓ x₀∉x₁s

--pattern ⟦_⟧ x₀∉x₁s = ✓ x₀∉x₁s

data ∅⊂_ {𝐴 : Set} : 𝕃 𝐴 → Set where
  ✓ : ∀ {x₀ x₁s} → (x₀∉x₁s : x₀ ∉ x₁s) → ∅⊂ ✓ x₀∉x₁s

pattern tail= x₁s = ✓ {x₁s = x₁s} _
pattern [_] x₀ = ✓ {x₀ = x₀} ∅
pattern _₀∷₁_∷⟦_⟧ x₀ x₁ x₂s = ✓ {x₀ = x₀} (● {x₁} _ {x₂s} _ _)

pattern _↶_↷_ x₀∉x₂s x₀≢x₁ x₁∉x₂s = ● x₀≢x₁ x₀∉x₂s x₁∉x₂s

𝕃→𝑳 : ∀ {𝐴 : Set} → 𝕃 𝐴 → 𝑳 𝐴
𝕃→𝑳 ∅ = ∅
𝕃→𝑳 [ x ] = x ∷ₗ ∅
𝕃→𝑳 (x₀ ₀∷₁ x₁ ∷⟦ x₂s ⟧) = x₀ ∷ₗ x₁ ∷ₗ 𝕃→𝑳 x₂s

data _∈_ {𝐴 : Set} (𝔞 : 𝐴) : 𝕃 𝐴 → Set where
  here : ∀ {x₀s} (𝔞∉x₀s : 𝔞 ∉ x₀s) → 𝔞 ∈ ✓ 𝔞∉x₀s
  there : ∀ {x₁s} → (𝔞∈x₁s : 𝔞 ∈ x₁s) → ∀ {x₀} → (x₀∉x₁s : x₀ ∉ x₁s)  → 𝔞 ∈ ✓ x₀∉x₁s

data _[_]=_ {𝐴 : Set} : 𝕃 𝐴 → ℕ → 𝐴 → Set where
  here  : ∀ {𝔞 xs} (𝔞∉xs : 𝔞 ∉ xs) → ✓ 𝔞∉xs [ 0 ]= 𝔞
  there : ∀ {x₀ x₁s} (x₀∉x₁s : x₀ ∉ x₁s) {i 𝔞} (x₁s[i]=𝔞 : x₁s [ i ]= 𝔞) → ✓ x₀∉x₁s [ suc i ]= 𝔞

⊥-𝕃[i]=x∉𝕃 : ∀ {𝐴 : Set} {L : 𝕃 𝐴} {n} {a} → L [ n ]= a → a ∉ L → ⊥
⊥-𝕃[i]=x∉𝕃 (here _) (_ ↶ x ↷ _) = x refl
⊥-𝕃[i]=x∉𝕃 (there _ x) (x₂ ↶ _ ↷ _) = ⊥-𝕃[i]=x∉𝕃 x x₂

lastIndex : ∀ {𝐴 : Set} {L : 𝕃 𝐴} (∅⊂L : ∅⊂ L) → ℕ
lastIndex [ _ ] = 0
lastIndex (✓ (_ ↶ _ ↷ x₀∉x₁s)) = suc (lastIndex (✓ x₀∉x₁s))

length : ∀ {𝐴 : Set} → 𝕃 𝐴 → ℕ
length ∅ = 0
length (tail= x₁s) = suc (length x₁s)

sym≢ : ∀ {𝐴 : Set} {x y : 𝐴} → x ≢ y → y ≢ x
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

last : ∀ {𝐴 : Set} {L} → ∅⊂ L → 𝐴
last [ x₀ ] = x₀
last (tail= (✓ x₁∉x₂s)) = last $! (∅⊂_.✓ x₁∉x₂s)

_[lastIndex]=last : ∀ {𝐴 : Set} {L : 𝕃 𝐴} → (∅⊂L : ∅⊂ L) → L [ lastIndex ∅⊂L ]= last ∅⊂L
[ _ ] [lastIndex]=last = here ∅
(✓ (x₀∉x₁s₁ ↶ x ↷ x₀∉x₁s)) [lastIndex]=last = there (x₀∉x₁s₁ ↶ x ↷ x₀∉x₁s) (✓ x₀∉x₁s [lastIndex]=last)

open import Prelude.Product
--open import Products

mutual
  init : ∀ {𝐴 : Set} {x₀s : 𝕃 𝐴} (∅⊂x₀s : ∅⊂ x₀s) → 𝕃 𝐴
  init [ _ ] = ∅
--  init (✓ (x₀∉x₂s ↶ _ ↷ x₁∉x₂s)) = ✓ (init∉ (✓ _) $! (x₀∉x₂s ↶ _ ↷ x₁∉x₂s))
  init (✓ (x₀∉x₂s ↶ x₁≢x₀ ↷ x₁∉x₂s)) = ✓ ((init∉ $! (✓ _)) $! (● x₁≢x₀ x₀∉x₂s x₁∉x₂s))

  init∉ : ∀ {𝐴 : Set} {x₀ : 𝐴} {x₁s : 𝕃 𝐴} (∅⊂x₁s : ∅⊂ x₁s) → x₀ ∉ x₁s → x₀ ∉ init ∅⊂x₁s
  init∉ () ∅
  init∉ (✓ _) (∅ ↶ _ ↷ ∅) = ∅
--  init∉ (✓ _) ((x₀∉x₃s ↶ x₀≢x₂ ↷ x₂∉x₃s) ↶ x₀≢x₁ ↷ (x₁∉x₃s ↶ x₁≢x₂ ↷ .x₂∉x₃s)) = (init∉ _ $! (x₀∉x₃s ↶ x₀≢x₂ ↷ x₂∉x₃s)) ↶ x₀≢x₁ ↷ ((uncurry init∉) $! (_ , (x₁∉x₃s ↶ x₁≢x₂ ↷ x₂∉x₃s)))
--  init∉ (✓ _) ((x₀∉x₃s ↶ x₀≢x₂ ↷ x₂∉x₃s) ↶ x₀≢x₁ ↷ (x₁∉x₃s ↶ x₁≢x₂ ↷ .x₂∉x₃s)) = (uncurry init∉) (_ , ((x₀∉x₃s ↶ x₀≢x₂ ↷ x₂∉x₃s)) ↶ x₀≢x₁ ↷ ((uncurry init∉) (_ , (x₁∉x₃s ↶ x₁≢x₂ ↷ x₂∉x₃s))))
  init∉ (✓ _) ((● x₀≢x₂ x₀∉x₃s x₂∉x₃s) ↶ x₀≢x₁ ↷ (x₁∉x₃s ↶ x₁≢x₂ ↷ .x₂∉x₃s)) = (init∉ _ $! (((● x₀≢x₂) $! x₀∉x₃s) $! x₂∉x₃s)) ↶ x₀≢x₁ ↷ ((uncurry init∉) $! (_ , (x₁∉x₃s ↶ x₁≢x₂ ↷ x₂∉x₃s)))


postulate
  magic : ∀ {𝐴 : Set} → 𝐴

rotateDown∉ : ∀ {𝐴 : Set} {xs : 𝕃 𝐴} (∅⊂xs : ∅⊂ xs) → (last ∅⊂xs) ∉ (init ∅⊂xs)
rotateDown∉ [ _ ] = ∅
rotateDown∉ (✓ (x₀∉x₂s ↶ x₀≢x₁ ↷ x₁∉x₂s)) =
  let xₙ≢x₀ = λ lastx₁s≡x₀ → let x₁s[last]=x₀ : ✓ x₁∉x₂s [ lastIndex (✓ x₁∉x₂s) ]= _
                                 x₁s[last]=x₀ = subst (✓ x₁∉x₂s [ lastIndex (✓ x₁∉x₂s) ]=_) lastx₁s≡x₀ $! (✓ x₁∉x₂s [lastIndex]=last)
                             in
                               (uncurry $! ⊥-𝕃[i]=x∉𝕃) $! (x₁s[last]=x₀ , (x₀∉x₂s ↶ x₀≢x₁ ↷ x₁∉x₂s))
  in
    (rotateDown∉ $! (∅⊂_.✓ x₁∉x₂s)) ↶ xₙ≢x₀ ↷ (init∉ (∅⊂_.✓ x₁∉x₂s) $! (x₀∉x₂s ↶ x₀≢x₁ ↷ x₁∉x₂s))
--    (rotateDown∉ $! (∅⊂_.✓ x₁∉x₂s)) ↶ xₙ≢x₀ ↷ ((uncurry init∉) $! (_,_ $! (∅⊂_.✓ x₁∉x₂s)) $! (x₀∉x₂s ↶ x₀≢x₁ ↷ x₁∉x₂s))
--    (rotateDown∉ (∅⊂_.✓ x₁∉x₂s)) ↶ xₙ≢x₀ ↷ (init∉ (∅⊂_.✓ x₁∉x₂s) (● x₀≢x₁ x₀∉x₂s x₁∉x₂s))
--    (rotateDown∉ (∅⊂_.✓ x₁∉x₂s)) ↶ xₙ≢x₀ ↷ (init∉ (∅⊂_.✓ x₁∉x₂s) (● x₀≢x₁ x₀∉x₂s x₁∉x₂s))
--    (rotateDown∉ (∅⊂_.✓ x₁∉x₂s)) ↶ magic ↷ (init∉ (∅⊂_.✓ x₁∉x₂s) (● x₀≢x₁ x₀∉x₂s x₁∉x₂s))
--    (rotateDown∉ (∅⊂_.✓ x₁∉x₂s)) ↶ magic ↷ (init∉ (∅⊂_.✓ x₁∉x₂s) (● x₀≢x₁ x₀∉x₂s x₁∉x₂s))

-- rotateDown "A12345678Z" = "ZA12345678"
rotateDown : ∀ {𝐴 : Set} → 𝕃 𝐴 → 𝕃 𝐴
rotateDown ∅ = ∅
--rotateDown [ x₀ ] = [ x₀ ]
rotateDown [ x₀ ] = [_] $! x₀
rotateDown (✓ x₀∉x₁s) = 𝕃.✓ $! (rotateDown∉ $! (∅⊂_.✓ $! x₀∉x₁s))

rotateDown-ex : 𝕃→𝑳 (rotateDown [abcd]) ≡ (⋆d ∷ₗ ⋆a ∷ₗ ⋆b ∷ₗ ⋆c ∷ₗ ∅)
rotateDown-ex = refl

-- memory hog
test-rotateDown₂₄ : 𝕃→𝑳 (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown [abcd])))))))))))))))))))))))) ≡ 𝕃→𝑳 [abcd]
test-rotateDown₂₄ = {!refl!}

test-rotateDown₄' : 𝕃→𝑳 (rotateDown $! rotateDown $! rotateDown $! rotateDown $! [abcd]) ≡ 𝕃→𝑳 [abcd]
test-rotateDown₄' = refl

-- memory hog
test-rotateDown₂₄' : 𝕃→𝑳 (rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! rotateDown $! [abcd]) ≡ 𝕃→𝑳 [abcd]
test-rotateDown₂₄' = {!refl!}
