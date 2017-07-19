---
-- absurdity, falsehood, or bottom
---

data ⊥ : Set where

---
-- characters
---

data Character : Set where
  A B C D E F G H I J K L M N O P Q R S T U V W X Y Z space : Character

infix 10 _≡Character_
data _≡Character_ (c : Character) : Character → Set where
  equal : c ≡Character c

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
toNaturalnumber A = 1
toNaturalnumber B = 2
toNaturalnumber C = 3
toNaturalnumber D = 4
toNaturalnumber E = 5
toNaturalnumber F = 6
toNaturalnumber G = 7
toNaturalnumber H = 8
toNaturalnumber I = 9
toNaturalnumber J = 10
toNaturalnumber K = 11
toNaturalnumber L = 12
toNaturalnumber M = 13
toNaturalnumber N = 14
toNaturalnumber O = 15
toNaturalnumber P = 16
toNaturalnumber Q = 17
toNaturalnumber R = 18
toNaturalnumber S = 19
toNaturalnumber T = 20
toNaturalnumber U = 21
toNaturalnumber V = 22
toNaturalnumber W = 23
toNaturalnumber X = 24
toNaturalnumber Y = 25
toNaturalnumber Z = 26
toNaturalnumber space = 0

_ : toNaturalnumber A ≡Naturalnumber 1
_ = equal

_ : toNaturalnumber B ≡Naturalnumber 2
_ = equal

_ : toNaturalnumber Z ≡Naturalnumber 26
_ = equal

_ : toNaturalnumber space ≡Naturalnumber 0
_ = equal

fromNaturalnumber
  : Naturalnumber
  → Character
fromNaturalnumber 0 = space
fromNaturalnumber 1 = A
fromNaturalnumber 2 = B
fromNaturalnumber 3 = C
fromNaturalnumber 4 = D
fromNaturalnumber 5 = E
fromNaturalnumber 6 = F
fromNaturalnumber 7 = G
fromNaturalnumber 8 = H
fromNaturalnumber 9 = I
fromNaturalnumber 10 = J
fromNaturalnumber 11 = K
fromNaturalnumber 12 = L
fromNaturalnumber 13 = M
fromNaturalnumber 14 = N
fromNaturalnumber 15 = O
fromNaturalnumber 16 = P
fromNaturalnumber 17 = Q
fromNaturalnumber 18 = R
fromNaturalnumber 19 = S
fromNaturalnumber 20 = T
fromNaturalnumber (successor 20) = U
fromNaturalnumber (successor (successor 20)) = V
fromNaturalnumber (successor (successor (successor 20))) = W
fromNaturalnumber (successor (successor (successor (successor 20)))) = X
fromNaturalnumber (successor (successor (successor (successor (successor 20))))) = Y
fromNaturalnumber (successor (successor (successor (successor (successor (successor 20)))))) = Z
fromNaturalnumber (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor (successor x))))))))))))))))))))))))))) = fromNaturalnumber x

_ : fromNaturalnumber 0 ≡Character space
_ = equal

_ : fromNaturalnumber 1 ≡Character A
_ = equal

_ : fromNaturalnumber 26 ≡Character Z
_ = equal

_ : fromNaturalnumber 30 ≡Character fromNaturalnumber (30 - 27)
_ = equal

_ : fromNaturalnumber 30 ≡Character fromNaturalnumber 3
_ = equal

_ : fromNaturalnumber 30 ≡Character C
_ = equal

to-and-fro-Naturalnumber : ∀ c → fromNaturalnumber (toNaturalnumber c) ≡Character c
to-and-fro-Naturalnumber A = equal
to-and-fro-Naturalnumber B = equal
to-and-fro-Naturalnumber C = equal
to-and-fro-Naturalnumber D = equal
to-and-fro-Naturalnumber E = equal
to-and-fro-Naturalnumber F = equal
to-and-fro-Naturalnumber G = equal
to-and-fro-Naturalnumber H = equal
to-and-fro-Naturalnumber I = equal
to-and-fro-Naturalnumber J = equal
to-and-fro-Naturalnumber K = equal
to-and-fro-Naturalnumber L = equal
to-and-fro-Naturalnumber M = equal
to-and-fro-Naturalnumber N = equal
to-and-fro-Naturalnumber O = equal
to-and-fro-Naturalnumber P = equal
to-and-fro-Naturalnumber Q = equal
to-and-fro-Naturalnumber R = equal
to-and-fro-Naturalnumber S = equal
to-and-fro-Naturalnumber T = equal
to-and-fro-Naturalnumber U = equal
to-and-fro-Naturalnumber V = equal
to-and-fro-Naturalnumber W = equal
to-and-fro-Naturalnumber X = equal
to-and-fro-Naturalnumber Y = equal
to-and-fro-Naturalnumber Z = equal
to-and-fro-Naturalnumber space = equal

fro-and-to-Naturalnumber : ∀ n → toNaturalnumber (fromNaturalnumber n) ≡Naturalnumber n
fro-and-to-Naturalnumber 0 = equal
fro-and-to-Naturalnumber 1 = equal
fro-and-to-Naturalnumber 2 = equal
fro-and-to-Naturalnumber 3 = equal
fro-and-to-Naturalnumber 4 = equal
fro-and-to-Naturalnumber 5 = equal
fro-and-to-Naturalnumber 6 = equal
fro-and-to-Naturalnumber 7 = equal
fro-and-to-Naturalnumber 8 = equal
fro-and-to-Naturalnumber 9 = equal
fro-and-to-Naturalnumber 10 = equal
fro-and-to-Naturalnumber 11 = equal
fro-and-to-Naturalnumber 12 = equal
fro-and-to-Naturalnumber 13 = equal
fro-and-to-Naturalnumber 14 = equal
fro-and-to-Naturalnumber 15 = equal
fro-and-to-Naturalnumber 16 = equal
fro-and-to-Naturalnumber 17 = equal
fro-and-to-Naturalnumber 18 = equal
fro-and-to-Naturalnumber 19 = equal
fro-and-to-Naturalnumber 20 = equal
fro-and-to-Naturalnumber (successor 20) = equal
fro-and-to-Naturalnumber (successor (successor 20)) = equal
fro-and-to-Naturalnumber (successor (successor (successor 20))) = equal
fro-and-to-Naturalnumber (successor (successor (successor (successor 20)))) = equal
fro-and-to-Naturalnumber (successor (successor (successor (successor (successor 20))))) = equal
fro-and-to-Naturalnumber (successor (successor (successor (successor (successor (successor 20)))))) = equal
fro-and-to-Naturalnumber (successor (successor (successor (successor (successor (successor (successor 20))))))) = {!!}
fro-and-to-Naturalnumber (successor n) = {!!}

shiftRightOne : Character → Character
shiftRightOne c = fromNaturalnumber (successor (toNaturalnumber c))

{-
shiftRightOne A = B
shiftRightOne B = C
shiftRightOne C = D
shiftRightOne D = E
shiftRightOne E = F
shiftRightOne F = G
shiftRightOne G = H
shiftRightOne H = I
shiftRightOne I = J
shiftRightOne J = K
shiftRightOne K = L
shiftRightOne L = M
shiftRightOne M = N
shiftRightOne N = O
shiftRightOne O = P
shiftRightOne P = Q
shiftRightOne Q = R
shiftRightOne R = S
shiftRightOne S = T
shiftRightOne T = U
shiftRightOne U = V
shiftRightOne V = W
shiftRightOne W = X
shiftRightOne X = Y
shiftRightOne Y = Z
shiftRightOne Z = space
shiftRightOne space = A
-}

shiftLeftOne : Character → Character
shiftLeftOne c = fromNaturalnumber (26 + toNaturalnumber c)
{-
shiftLeftOne A = space
shiftLeftOne B = A
shiftLeftOne C = B
shiftLeftOne D = C
shiftLeftOne E = D
shiftLeftOne F = E
shiftLeftOne G = F
shiftLeftOne H = G
shiftLeftOne I = H
shiftLeftOne J = I
shiftLeftOne K = J
shiftLeftOne L = K
shiftLeftOne M = L
shiftLeftOne N = M
shiftLeftOne O = N
shiftLeftOne P = O
shiftLeftOne Q = P
shiftLeftOne R = Q
shiftLeftOne S = R
shiftLeftOne T = S
shiftLeftOne U = T
shiftLeftOne V = U
shiftLeftOne W = V
shiftLeftOne X = W
shiftLeftOne Y = X
shiftLeftOne Z = Y
shiftLeftOne space = Z
-}

-- _ : ∀ n → fromNaturalnumber (n + 27) ≡Character fromNaturalnumber n

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

_ : decryptCharacter F 2 ≡Character D
_ = equal

-- shiftD : shiftLeftOne

lemma1 : ∀ cᵢ cₒ n → decryptCharacter cᵢ n ≡Character cₒ → shiftLeftOne (decryptCharacter (shiftRightOne cᵢ) n) ≡Character cₒ
lemma1 A .A zero equal = {!!}
lemma1 B .B zero equal = {!!}
lemma1 C .C zero equal = {!!}
lemma1 D .D zero equal = {!!}
lemma1 E .E zero equal = {!!}
lemma1 F .F zero equal = {!!}
lemma1 G .G zero equal = {!!}
lemma1 H .H zero equal = {!!}
lemma1 I .I zero equal = {!!}
lemma1 J .J zero equal = {!!}
lemma1 K .K zero equal = {!!}
lemma1 L .L zero equal = {!!}
lemma1 M .M zero equal = {!!}
lemma1 N .N zero equal = {!!}
lemma1 O .O zero equal = {!!}
lemma1 P .P zero equal = {!!}
lemma1 Q .Q zero equal = {!!}
lemma1 R .R zero equal = {!!}
lemma1 S .S zero equal = {!!}
lemma1 T .T zero equal = {!!}
lemma1 U .U zero equal = {!!}
lemma1 V .V zero equal = {!!}
lemma1 W .W zero equal = {!!}
lemma1 X .X zero equal = {!!}
lemma1 Y .Y zero equal = {!!}
lemma1 Z .Z zero equal = {!!}
lemma1 space .space zero equal = {!!}
lemma1 cᵢ .(shiftLeftOne cᵢ) (successor zero) equal = {!!}
lemma1 cᵢ .(shiftLeftOne (decryptCharacter cᵢ (successor n))) (successor (successor n)) equal = {!!}

lemma : ∀ c n →
  decryptCharacter (shiftRightOne (encryptCharacter c (successor n))) (successor n)
    ≡Character
  shiftRightOne c
lemma c zero = {!!}
lemma c (successor n) = {!lemma c n!}

characterDecryptionIsSound :
  ∀ c n
  → decryptCharacter (encryptCharacter c n) n ≡Character c
characterDecryptionIsSound c zero = equal
characterDecryptionIsSound c (successor zero) = {!!}
characterDecryptionIsSound c (successor (successor n)) = {!!}

-- strings

data String : Set where
  empty : String
  _∷_ : Character → String → String
infixr 20 _∷_

infix 10 _≡String_
data _≡String_ (s : String) : String → Set where
  equal : s ≡String s

_ : A ∷ B ∷ empty ≡String A ∷ B ∷ empty
_ = equal

encryptString
  : String
  → Naturalnumber
  → String
encryptString empty _ = empty
encryptString (c ∷ s) n = encryptCharacter c n ∷ encryptString s n

decryptString
  : String
  → Naturalnumber
  → String
decryptString empty _ = empty
decryptString (c ∷ s) n = decryptCharacter c n ∷ decryptString s n

_ : A ∷ B ∷ empty ≡String A ∷ C ∷ empty → ⊥
_ = λ ()

congruencyOfChar∷String
  : ∀ c₁ c₂ s₁ s₂
  → c₁ ≡Character c₂
  → s₁ ≡String s₂
  → c₁ ∷ s₁ ≡String c₂ ∷ s₂
congruencyOfChar∷String _ _ _ _ equal equal = equal

stringDecryptionIsSound :
  ∀ s n
  → decryptString (encryptString s n) n ≡String s
stringDecryptionIsSound empty n = equal
stringDecryptionIsSound (c ∷ s) n =
  let charEqual = characterDecryptionIsSound c n
      stringEqual = stringDecryptionIsSound s n
  in congruencyOfChar∷String
       (decryptCharacter (encryptCharacter c n) n)
       c
       (decryptString (encryptString s n) n)
       s
       charEqual
       stringEqual
