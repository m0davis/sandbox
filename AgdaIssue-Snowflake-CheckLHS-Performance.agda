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

open import Prelude using (id {-syntax ofType-})
[a]    = ✓ a∅    ofType 𝕃 T
[ab]   = ✓ a∉b   ofType 𝕃 T
[ba]   = ✓ b∉a   ofType 𝕃 T
[abc]  = ✓ a∉bc  ofType 𝕃 T
[cab]  = ✓ c∉ab  ofType 𝕃 T
[cba]  = ✓ c∉ba  ofType 𝕃 T
[abcd] = ✓ a∉bcd ofType 𝕃 T
[dcab] = ✓ d∉cab ofType 𝕃 T
[dcba] = ✓ d∉cba ofType 𝕃 T

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

rotate∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {xs : 𝕃 𝐴} (∅⊂xs : ∅⊂ xs) → last ∅⊂xs ∉ init ∅⊂xs
rotate∉ [ _ ] = ∅
rotate∉ (✓ (x₀∉x₂s ↶ x₀≢x₁ ↷ x₁∉x₂s)) =
  let xₙ≢x₀ = λ lastx₁s≡x₀ → let x₁s[last]=x₀ : ✓ x₁∉x₂s [ lastIndex (✓ x₁∉x₂s) ]= _
                                 x₁s[last]=x₀ = subst (✓ x₁∉x₂s [ lastIndex (✓ x₁∉x₂s) ]=_) lastx₁s≡x₀ (✓ x₁∉x₂s [lastIndex]=last)
                             in
                               ⊥-𝕃[i]=x∉𝕃 x₁s[last]=x₀ (x₀∉x₂s ↶ x₀≢x₁ ↷ x₁∉x₂s)
  in
    rotate∉ (✓ x₁∉x₂s) ↶ xₙ≢x₀ ↷ init∉ (✓ x₁∉x₂s) (x₀∉x₂s ↶ x₀≢x₁ ↷ x₁∉x₂s)

-- rotate "0123456789" = "9012345678"
rotate : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → 𝕃 𝐴
rotate ∅ = ∅
rotate [ x₀ ] = [ x₀ ]
rotate (✓ x₀∉x₁s) = ✓ (rotate∉ (✓ x₀∉x₁s))

rotate-ex : 𝕃→𝑳 (rotate [abcd]) ≡ (⋆d ∷ₗ ⋆a ∷ₗ ⋆b ∷ₗ ⋆c ∷ₗ ∅)
rotate-ex = refl

-- reseal "0123456789" = "1023456789"
reseal : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → 𝕃 𝐴
reseal ∅ = ∅
reseal [ x₀ ] = [ x₀ ]
reseal (✓ (x₀∉x₂s ↶ x₀≢x₁ ↷ x₁∉x₂s)) = ✓ (x₁∉x₂s ↶ sym≢ x₀≢x₁ ↷ x₀∉x₂s)

reseal-ex : 𝕃→𝑳 (reseal [abcd]) ≡ (⋆b ∷ₗ ⋆a ∷ₗ ⋆c ∷ₗ ⋆d ∷ₗ ∅)
reseal-ex = refl

-- rotateBy 2 "0123456789" = "8901234567"
-- rotateBy 3 s = rotate (rotate (rotate s))
rotateBy : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
rotateBy 0 x = x
rotateBy (suc n) x = x |⋙ rotate ⋙ rotateBy n

rotateBy-ex : 𝕃→𝑳 (rotateBy 2 [abcd]) ≡ (⋆c ∷ₗ ⋆d ∷ₗ ⋆a ∷ₗ ⋆b ∷ₗ ∅)
rotateBy-ex = refl

-- resealTa 3 "0123456789" = "0123465789"
-- i.e. take the 3rd (indexed-from-the-right) item (6) and move it one space to the left
-- resealTa (lastIndex s - 1) s = reseal s
resealTa : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
resealTa _ ∅ = ∅
resealTa _ [ x₀ ] = [ x₀ ]
resealTa n xs = xs |⋙ rotateBy (2 + n) ⋙ reseal ⋙ rotateBy (length xs - 2 - n)

resealTa-ex : 𝕃→𝑳 (resealTa 2 [abcd]) ≡ (⋆b ∷ₗ ⋆a ∷ₗ ⋆c ∷ₗ ⋆d ∷ₗ ∅)
resealTa-ex = refl

-- resealTaBy 2 "0123456789" = "0123456978"
-- i.e. take the last item (9) and move it 2 spaces to the left
resealTaBy : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
resealTaBy _ ∅ = ∅
resealTaBy _ [ x₀ ] = [ x₀ ]
resealTaBy 0 xs = xs
resealTaBy (suc n) xs = xs |⋙ resealTaBy n ⋙ resealTa n

resealTaBy-ex : 𝕃→𝑳 (resealTaBy 2 [abcd]) ≡ (⋆a ∷ₗ ⋆d ∷ₗ ⋆b ∷ₗ ⋆c ∷ₗ ∅)
resealTaBy-ex = refl

-- resealAtBy 6 2 "0123456789" = "0123456789"
-- i.e. take the 6th (indexed-from-the-left) item (6) and move it 2 places to the left
-- resealAtBy 1 1 = reseal
resealAtBy : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → ℕ → 𝕃 𝐴 → 𝕃 𝐴
resealAtBy _ 0 xs = xs
resealAtBy n m xs with length xs
... | l with suc n ≟ l
... | yes _ = xs |⋙ resealTaBy m
... | no _  = xs |⋙ rotateBy (l - (suc n)) ⋙ resealTaBy m ⋙ rotateBy (suc n)

resealAtBy-ex : 𝕃→𝑳 (resealAtBy 2 2 [abcd]) ≡ (⋆c ∷ₗ ⋆a ∷ₗ ⋆b ∷ₗ ⋆d ∷ₗ ∅)
resealAtBy-ex = refl

reorder : ∀ {𝑨} {𝐴 : Set 𝑨} (L : 𝕃 𝐴) → 𝑳 ℕ → 𝕃 𝐴
reorder xs perm = go 0 perm xs where
  go : ∀ {𝑨} {𝐴 : Set 𝑨} → (n : ℕ) → 𝑳 ℕ → (L : 𝕃 𝐴) → 𝕃 𝐴
  go _ _ ∅ = ∅
  go _ ∅ xs = xs
  go n (p₀ ∷ₗ ps) xs = go (suc n) ps (resealAtBy (n + p₀) p₀ xs)

test₀ : 𝕃→𝑳 (reorder [abcd] (0 ∷ₗ 0 ∷ₗ 0 ∷ₗ 0 ∷ₗ ∅)) ≡ 𝕃→𝑳 [abcd]
test₀ = refl

--test₁ : 𝕃→𝑳 (reorder [abcd] (3 ∷ₗ 2 ∷ₗ 0 ∷ₗ 0 ∷ₗ ∅)) ≡ 𝕃→𝑳 [dcab]
--test₁ = refl

--test₂ : 𝕃→𝑳 (reorder [abcd] (3 ∷ₗ 2 ∷ₗ 1 ∷ₗ 0 ∷ₗ ∅)) ≡ 𝕃→𝑳 [dcba]
--test₂ = refl
