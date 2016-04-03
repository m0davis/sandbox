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

[a] = ✓ a∉∅
[ab] = ✓ a∉b
[ba] = ✓ b∉a
[abc] = ✓ a∉bc
[cab] = ✓ c∉ab
[cba] = ✓ c∉ba
[abcd] = ✓ a∉bcd
[dcab] = ✓ d∉cab
[dcba] = ✓ d∉cba

last : ∀ {𝑨} {𝐴 : Set 𝑨} {L} → ∅⊂ L → 𝐴
last (∅⊂∷ {x₀} {∅} _) = x₀
last (∅⊂∷ {x₁s = ✓ x₁∉x₂s} _) = last (∅⊂∷ x₁∉x₂s)

last-thm₁ : ∀ {𝑨} {𝐴 : Set 𝑨} {L : 𝕃 𝐴} → (∅⊂L : ∅⊂ L) → L [ lastIndex ∅⊂L ]= last ∅⊂L
last-thm₁ (∅⊂∷ ∉∅) = here ∉∅
last-thm₁ (∅⊂∷ (∉∷ x x₀∉x₁s₁ x₀∉x₁s)) = there (∉∷ x x₀∉x₁s₁ x₀∉x₁s) (last-thm₁ (∅⊂∷ x₀∉x₁s))

mutual
  init : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀s : 𝕃 𝐴} (∅⊂x₀s : ∅⊂ x₀s) → 𝕃 𝐴
  init (∅⊂∷ ∉∅) = ∅
  init (∅⊂∷ (∉∷ _ x₀∉x₂s x₁∉x₂s)) = ✓ (init∉ (∅⊂∷ _) (∉∷ _ x₀∉x₂s x₁∉x₂s))

  init∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀ : 𝐴} {x₁s : 𝕃 𝐴} (∅⊂x₁s : ∅⊂ x₁s) → x₀ ∉ x₁s → x₀ ∉ init ∅⊂x₁s
  init∉ () ∉∅
  init∉ (∅⊂∷ _) (∉∷ _ ∉∅ ∉∅) = ∉∅
  init∉ (∅⊂∷ _) (∉∷ x₀≢x₁ (∉∷ x₀≢x₂ x₀∉x₃s x₂∉x₃s) (∉∷ x₁≢x₂ x₁∉x₃s .x₂∉x₃s)) = ∉∷ x₀≢x₁ (init∉ _ (∉∷ x₀≢x₂ x₀∉x₃s x₂∉x₃s)) (init∉ _ (∉∷ x₁≢x₂ x₁∉x₃s x₂∉x₃s))

rotate∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {xs : 𝕃 𝐴} (∅⊂xs : ∅⊂ xs) → last ∅⊂xs ∉ init ∅⊂xs
rotate∉ (∅⊂∷ ∉∅) = ∉∅
rotate∉ (∅⊂∷ {x₀} (∉∷ {x₁} x₀≢x₁ {x₂s} x₀∉x₂s x₁∉x₂s)) =
  let xₙ≢x₀ = let x₁s[last]=lastx₁s = last-thm₁ (∅⊂∷ x₁∉x₂s) in
                  λ lastx₁s≡x₀ →
                      let x₁s[last]=x₀ : ✓ x₁∉x₂s [ lastIndex (∅⊂∷ x₁∉x₂s) ]= x₀
                          x₁s[last]=x₀ = subst (✓ x₁∉x₂s [ lastIndex (∅⊂∷ x₁∉x₂s) ]=_) lastx₁s≡x₀ x₁s[last]=lastx₁s
                      in []=-thm₀ x₁s[last]=x₀ (∉∷ x₀≢x₁ x₀∉x₂s x₁∉x₂s)
  in
    ∉∷ xₙ≢x₀
       (rotate∉ (∅⊂∷ x₁∉x₂s))
       (init∉ (∅⊂∷ x₁∉x₂s) (∉∷ x₀≢x₁ x₀∉x₂s x₁∉x₂s))

-- rotate "0123456789" = "9012345678"
rotate : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → 𝕃 𝐴
rotate ∅ = ∅
rotate [ x₀ ] = [ x₀ ]
rotate (✓ x₀∉x₁s) = ✓ (rotate∉ (∅⊂∷ x₀∉x₁s))

rotate-ex : 𝕃→𝑳 (rotate [abcd]) ≡ (⋆d ∷ₗ ⋆a ∷ₗ ⋆b ∷ₗ ⋆c ∷ₗ ∅)
rotate-ex = refl

-- reseal "0123456789" = "1023456789"
reseal : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → 𝕃 𝐴
reseal ∅ = ∅
reseal [ x₀ ] = [ x₀ ]
reseal (✓ (∉∷ x₀≢x₁ x₀∉x₂s x₁∉x₂s)) = ✓ (∉∷ (sym' x₀≢x₁) x₁∉x₂s x₀∉x₂s)

reseal-ex : 𝕃→𝑳 (reseal [abcd]) ≡ (⋆b ∷ₗ ⋆a ∷ₗ ⋆c ∷ₗ ⋆d ∷ₗ ∅)
reseal-ex = refl

-- rotateBy 2 "0123456789" = "8901234567"
-- rotateBy 3 s = rotate (rotate (rotate s))
rotateBy : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
rotateBy 0 x = x
rotateBy (suc n) x = rotateBy n (rotate x)

rotateBy-ex : 𝕃→𝑳 (rotateBy 2 [abcd]) ≡ (⋆c ∷ₗ ⋆d ∷ₗ ⋆a ∷ₗ ⋆b ∷ₗ ∅)
rotateBy-ex = refl

-- resealTa 3 "0123456789" = "0123465789"
-- i.e. take the 3rd (indexed-from-the-right) item (6) and move it one space to the left
-- resealTa (lastIndex s - 1) s = reseal s
resealTa : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
resealTa _ ∅ = ∅
resealTa _ [ x₀ ] = [ x₀ ]
resealTa n xs = rotateBy (length xs - 2 - n) (reseal (rotateBy (2 + n) xs))

resealTa-ex : 𝕃→𝑳 (resealTa 2 [abcd]) ≡ (⋆b ∷ₗ ⋆a ∷ₗ ⋆c ∷ₗ ⋆d ∷ₗ ∅)
resealTa-ex = refl

-- resealTaBy 2 "0123456789" = "0123456978"
-- i.e. take the last item (9) and move it 2 spaces to the left
resealTaBy : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
resealTaBy _ ∅ = ∅
resealTaBy _ [ x₀ ] = [ x₀ ]
resealTaBy 0 xs = xs
resealTaBy (suc n) xs = resealTa n (resealTaBy n xs)

resealTaBy-ex : 𝕃→𝑳 (resealTaBy 2 [abcd]) ≡ (⋆a ∷ₗ ⋆d ∷ₗ ⋆b ∷ₗ ⋆c ∷ₗ ∅)
resealTaBy-ex = refl

-- resealAtBy 6 2 "0123456789" = "0123456789"
-- i.e. take the 6th (indexed-from-the-left) item (6) and move it 2 places to the left
-- resealAtBy 1 1 = reseal
resealAtBy : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → ℕ → 𝕃 𝐴 → 𝕃 𝐴
resealAtBy _ 0 xs = xs
resealAtBy n m xs with length xs
... | l with suc n ≟ l
... | yes _ =                   resealTaBy m (                       xs)
... | no _  = rotateBy (suc n) (resealTaBy m (rotateBy (l - (suc n)) xs))

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
