---
-- absurdity, falsehood, or bottom
---

data ⊥ : Set where

---
-- characters
---

data Character : Set where
  space A B C D : Character

infix 10 _≡Character_
data _≡Character_ (c : Character) : Character → Set where
  equal : c ≡Character c

transitivity≡Character :
  ∀ {c₁ c₂ c₃}
  → c₁ ≡Character c₂
  → c₂ ≡Character c₃
  → c₁ ≡Character c₃
transitivity≡Character equal c₂≡c₃ = c₂≡c₃

symmetry≡Character :
  ∀ {c₁ c₂}
  → c₁ ≡Character c₂
  → c₂ ≡Character c₁
symmetry≡Character equal = equal

substitute≡Character :
  ∀ {c₁ c₂}
  (P : Character → Set)
  → c₁ ≡Character c₂
  → P c₁
  → P c₂
substitute≡Character _ equal Pc₁ = Pc₁

---
-- numbers
---

data Naturalnumber : Set where
  zero : Naturalnumber
  successor : Naturalnumber → Naturalnumber

{-# BUILTIN NATURAL Naturalnumber #-}

infix 10 _≡Naturalnumber_
data _≡Naturalnumber_ (n : Naturalnumber) : Naturalnumber → Set where
  equal : n ≡Naturalnumber n

_-_ : Naturalnumber
    → Naturalnumber
    → Naturalnumber
x - zero = x
zero - successor _ = zero -- if m is greater than n, then n - m = 0
successor x - successor y = x - y

_+_ : Naturalnumber
    → Naturalnumber
    → Naturalnumber
zero + y = y
successor x + y = x + successor y

---
-- conversions between characters and numbers
---

toNaturalnumber
  : Character
  → Naturalnumber
toNaturalnumber space = 0
toNaturalnumber A = 1
toNaturalnumber B = 2
toNaturalnumber C = 3
toNaturalnumber D = 4

_ : toNaturalnumber space ≡Naturalnumber 0
_ = equal

_ : toNaturalnumber A ≡Naturalnumber 1
_ = equal

_ : toNaturalnumber B ≡Naturalnumber 2
_ = equal

fromNaturalnumber
  : Naturalnumber
  → Character
fromNaturalnumber 0 = space
fromNaturalnumber 1 = A
fromNaturalnumber 2 = B
fromNaturalnumber 3 = C
fromNaturalnumber 4 = D
fromNaturalnumber (successor (successor (successor (successor (successor x))))) = fromNaturalnumber x

_ : fromNaturalnumber 0 ≡Character space
_ = equal

_ : fromNaturalnumber 1 ≡Character A
_ = equal

_ : fromNaturalnumber 4 ≡Character D
_ = equal

_ : fromNaturalnumber 7 ≡Character fromNaturalnumber (7 - 5)
_ = equal

_ : fromNaturalnumber 7 ≡Character fromNaturalnumber 2
_ = equal

_ : fromNaturalnumber 7 ≡Character B
_ = equal

to-and-fro-Naturalnumber : ∀ c → fromNaturalnumber (toNaturalnumber c) ≡Character c
to-and-fro-Naturalnumber space = equal
to-and-fro-Naturalnumber A = equal
to-and-fro-Naturalnumber B = equal
to-and-fro-Naturalnumber C = equal
to-and-fro-Naturalnumber D = equal

{-
fro-and-to-Naturalnumber : ∀ n → toNaturalnumber (fromNaturalnumber n) ≡Naturalnumber n
fro-and-to-Naturalnumber 0 = equal
fro-and-to-Naturalnumber 1 = equal
fro-and-to-Naturalnumber 2 = equal
fro-and-to-Naturalnumber 3 = equal
fro-and-to-Naturalnumber 4 = equal
fro-and-to-Naturalnumber (successor (successor (successor (successor (successor x))))) = {!!}
-}

shiftRightOne : Character → Character
shiftRightOne c = fromNaturalnumber (successor (toNaturalnumber c))

shiftLeftOne : Character → Character
shiftLeftOne c = fromNaturalnumber (4 + toNaturalnumber c)

{-
data Coordinated (c : Character) :
  zero : P 0 → P 1 → P 2 → P 3 → P 4 → (∀ n → P n → P (5 + n)) →
-}

encryptCharacter
  : Character
  → Naturalnumber
  → Character
encryptCharacter c 0 = c
encryptCharacter c 1 = shiftRightOne c
encryptCharacter c (successor (successor n)) =
  shiftRightOne (encryptCharacter c (successor n))

_ : encryptCharacter A 3 ≡Character D
_ = equal

_ : encryptCharacter A 3 ≡Character D
_ = equal

decryptCharacter
  : Character
  → Naturalnumber
  → Character
decryptCharacter c zero = c
decryptCharacter c 1 = shiftLeftOne c
decryptCharacter c (successor (successor n)) = shiftLeftOne (decryptCharacter c (successor n))

_ : decryptCharacter A 2 ≡Character D
_ = equal

lemma3 : ∀ c → shiftRightOne (shiftRightOne (shiftRightOne (shiftRightOne (shiftRightOne c)))) ≡Character c
lemma3 space = equal
lemma3 A = equal
lemma3 B = equal
lemma3 C = equal
lemma3 D = equal

lemma2-char : ∀ c n → shiftRightOne (encryptCharacter c n) ≡Character encryptCharacter (shiftRightOne c) n
lemma2-char c zero = equal
lemma2-char c (successor zero) = equal
lemma2-char c (successor (successor zero)) = equal
lemma2-char c (successor (successor (successor zero))) = equal
lemma2-char c (successor (successor (successor (successor zero)))) = equal
lemma2-char c (successor (successor (successor (successor (successor zero))))) = equal
lemma2-char c (successor (successor (successor (successor (successor (successor n)))))) =
  let l2 = lemma2-char c (successor n)
      l31 = lemma3 (shiftRightOne (encryptCharacter c (successor n)))
      l32 = lemma3 (encryptCharacter (shiftRightOne c) (successor n))
  in transitivity≡Character l31 (transitivity≡Character l2 (symmetry≡Character l32))

lemma-char : ∀ c n → encryptCharacter c (1 + n) ≡Character encryptCharacter (shiftRightOne c) n
lemma-char c zero = equal
lemma-char c (successor n) = lemma2-char c (successor n)

lemma5d : ∀ c n → decryptCharacter c (5 + n) ≡Character decryptCharacter c n
lemma5d space zero = {!!}
lemma5d A zero = {!!}
lemma5d B zero = {!!}
lemma5d C zero = {!!}
lemma5d D zero = {!!}
lemma5d c (successor zero) = {!!}
lemma5d c (successor (successor zero)) = {!!}
lemma5d c (successor (successor (successor zero))) = {!!}
lemma5d c (successor (successor (successor (successor zero)))) = {!!}
lemma5d c (successor (successor (successor (successor (successor n))))) = {!!}

lemma5e : ∀ c n → encryptCharacter c (5 + n) ≡Character encryptCharacter c n
lemma5e c zero = {!!}
lemma5e c (successor n) = {!!}

characterDecryptionIsSound :
  ∀ c n
  → decryptCharacter (encryptCharacter c n) n ≡Character c
characterDecryptionIsSound c 0 = equal
characterDecryptionIsSound c 1 = {!decryptCharacter (shiftRightOne c) 1!}
characterDecryptionIsSound c 2 = {!decryptCharacter (shiftRightOne c) 1!}
characterDecryptionIsSound c 3 = {!decryptCharacter (shiftRightOne c) 1!}
characterDecryptionIsSound c 4 = {!decryptCharacter (shiftRightOne c) 1!}
characterDecryptionIsSound c (successor (successor (successor (successor (successor n))))) =
  let 5e = lemma5e c n
      5d = lemma5d (encryptCharacter c (5 + n)) n
  in transitivity≡Character 5d (substitute≡Character (λ c' → decryptCharacter c' n ≡Character c) (symmetry≡Character 5e) (characterDecryptionIsSound c n))

-- -- -- -- strings

-- -- -- data String : Set where
-- -- --   empty : String
-- -- --   _∷_ : Character → String → String
-- -- -- infixr 20 _∷_

-- -- -- infix 10 _≡String_
-- -- -- data _≡String_ (s : String) : String → Set where
-- -- --   equal : s ≡String s

-- -- -- _ : A ∷ B ∷ empty ≡String A ∷ B ∷ empty
-- -- -- _ = equal

-- -- -- encryptString
-- -- --   : String
-- -- --   → Naturalnumber
-- -- --   → String
-- -- -- encryptString empty _ = empty
-- -- -- encryptString (c ∷ s) n = encryptCharacter c n ∷ encryptString s n

-- -- -- decryptString
-- -- --   : String
-- -- --   → Naturalnumber
-- -- --   → String
-- -- -- decryptString empty _ = empty
-- -- -- decryptString (c ∷ s) n = decryptCharacter c n ∷ decryptString s n

-- -- -- _ : A ∷ B ∷ empty ≡String A ∷ C ∷ empty → ⊥
-- -- -- _ = λ ()

-- -- -- congruencyOfChar∷String
-- -- --   : ∀ c₁ c₂ s₁ s₂
-- -- --   → c₁ ≡Character c₂
-- -- --   → s₁ ≡String s₂
-- -- --   → c₁ ∷ s₁ ≡String c₂ ∷ s₂
-- -- -- congruencyOfChar∷String _ _ _ _ equal equal = equal

-- -- -- stringDecryptionIsSound :
-- -- --   ∀ s n
-- -- --   → decryptString (encryptString s n) n ≡String s
-- -- -- stringDecryptionIsSound empty n = equal
-- -- -- stringDecryptionIsSound (c ∷ s) n =
-- -- --   let charEqual = characterDecryptionIsSound c n
-- -- --       stringEqual = stringDecryptionIsSound s n
-- -- --   in congruencyOfChar∷String
-- -- --        (decryptCharacter (encryptCharacter c n) n)
-- -- --        c
-- -- --        (decryptString (encryptString s n) n)
-- -- --        s
-- -- --        charEqual
-- -- --        stringEqual
