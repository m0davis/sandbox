open import Prelude

data Character : Nat → Set where
  space : Character 0
  A     : Character 1
  B     : Character 2
  C     : Character 3
  D     : Character 4

data Characters : List Nat → Set where
  [] : Characters []
  _∷_ : ∀ {n ns} → Character n → Characters ns → Characters (n ∷ ns)

modChar : ∀ {n} → Character n → n mod 5 ≡ n
modChar space = refl
modChar A = refl
modChar B = refl
modChar C = refl
modChar D = refl

shift : ∀ {n} → Character n → Character ((1 + n) mod 5)
shift space = A
shift A = B
shift B = C
shift C = D
shift D = space

encode : ∀ {n} → Character n → (s : Nat) → Character ((s + n) mod 5)
encode c zero rewrite modChar c = c -- = transport Character (sym (modChar x)) x
encode c (suc zero) = shift c
encode c (suc (suc s)) = {!shift (encode c (suc s))!}


-- Naturalnumber = Nat

-- toNaturalnumber
--   : Character
--   → Naturalnumber
-- toNaturalnumber space = 0
-- toNaturalnumber A = 1
-- toNaturalnumber B = 2
-- toNaturalnumber C = 3
-- toNaturalnumber D = 4

-- fromNaturalnumber
--   : Naturalnumber
--   → Character
-- fromNaturalnumber 0 = space
-- fromNaturalnumber 1 = A
-- fromNaturalnumber 2 = B
-- fromNaturalnumber 3 = C
-- fromNaturalnumber 4 = D
-- fromNaturalnumber (suc (suc (suc (suc (suc x))))) = fromNaturalnumber x

-- to-and-fro-Naturalnumber : ∀ c → fromNaturalnumber (toNaturalnumber c) ≡ c
-- to-and-fro-Naturalnumber space = refl
-- to-and-fro-Naturalnumber A = refl
-- to-and-fro-Naturalnumber B = refl
-- to-and-fro-Naturalnumber C = refl
-- to-and-fro-Naturalnumber D = refl

-- shiftRightOne : Character → Character
-- shiftRightOne c = fromNaturalnumber (suc (toNaturalnumber c))

-- shiftLeftOne : Character → Character
-- shiftLeftOne c = fromNaturalnumber (4 + toNaturalnumber c)

-- encryptCharacter
--   : Character
--   → Naturalnumber
--   → Character
-- encryptCharacter c 0 = c
-- encryptCharacter c 1 = shiftRightOne c
-- encryptCharacter c (suc (suc n)) =
--   shiftRightOne (encryptCharacter c (suc n))

-- decryptCharacter
--   : Character
--   → Naturalnumber
--   → Character
-- decryptCharacter c zero = c
-- decryptCharacter c 1 = shiftLeftOne c
-- decryptCharacter c (suc (suc n)) = shiftLeftOne (decryptCharacter c (suc n))

-- shiftRight5≡id : ∀ c → shiftRightOne (shiftRightOne (shiftRightOne (shiftRightOne (shiftRightOne c)))) ≡ c
-- shiftRight5≡id space = refl
-- shiftRight5≡id A = refl
-- shiftRight5≡id B = refl
-- shiftRight5≡id C = refl
-- shiftRight5≡id D = refl

-- shiftRightOne∘encrypt≡encrypt∘shiftRightOne : ∀ c n → shiftRightOne (encryptCharacter c n) ≡ encryptCharacter (shiftRightOne c) n
-- shiftRightOne∘encrypt≡encrypt∘shiftRightOne c 0 = refl
-- shiftRightOne∘encrypt≡encrypt∘shiftRightOne c 1 = refl
-- shiftRightOne∘encrypt≡encrypt∘shiftRightOne c 2 = refl
-- shiftRightOne∘encrypt≡encrypt∘shiftRightOne c 3 = refl
-- shiftRightOne∘encrypt≡encrypt∘shiftRightOne c 4 = refl
-- shiftRightOne∘encrypt≡encrypt∘shiftRightOne c 5 = refl
-- shiftRightOne∘encrypt≡encrypt∘shiftRightOne c (suc (suc (suc (suc (suc (suc n)))))) =
--   let l2 = shiftRightOne∘encrypt≡encrypt∘shiftRightOne c (suc n)
--       l31 = shiftRight5≡id (shiftRightOne (encryptCharacter c (suc n)))
--       l32 = shiftRight5≡id (encryptCharacter (shiftRightOne c) (suc n))
--   in trans l31 (trans l2 (sym l32))

-- lemma-char : ∀ c n → encryptCharacter c (1 + n) ≡ encryptCharacter (shiftRightOne c) n
-- lemma-char c zero = refl
-- lemma-char c (suc n) = shiftRightOne∘encrypt≡encrypt∘shiftRightOne c (suc n)

-- lemma5e : ∀ c n → encryptCharacter c (5 + n) ≡ encryptCharacter c n
-- lemma5e c zero = {!!}
-- lemma5e c (suc n) = {!!}

-- -- lemma5d : ∀ c n → decryptCharacter c (5 + n) ≡Character decryptCharacter c n
-- -- lemma5d space zero = {!!}
-- -- lemma5d A zero = {!!}
-- -- lemma5d B zero = {!!}
-- -- lemma5d C zero = {!!}
-- -- lemma5d D zero = {!!}
-- -- lemma5d c (suc zero) = {!!}
-- -- lemma5d c (suc (suc zero)) = {!!}
-- -- lemma5d c (suc (suc (suc zero))) = {!!}
-- -- lemma5d c (suc (suc (suc (suc zero)))) = {!!}
-- -- lemma5d c (suc (suc (suc (suc (suc n))))) = {!!}

-- -- characterDecryptionIsSound :
-- --   ∀ c n
-- --   → decryptCharacter (encryptCharacter c n) n ≡Character c
-- -- characterDecryptionIsSound c 0 = refl
-- -- characterDecryptionIsSound c 1 = {!decryptCharacter (shiftRightOne c) 1!}
-- -- characterDecryptionIsSound c 2 = {!decryptCharacter (shiftRightOne c) 1!}
-- -- characterDecryptionIsSound c 3 = {!decryptCharacter (shiftRightOne c) 1!}
-- -- characterDecryptionIsSound c 4 = {!decryptCharacter (shiftRightOne c) 1!}
-- -- characterDecryptionIsSound c (suc (suc (suc (suc (suc n))))) =
-- --   let 5e = lemma5e c n
-- --       5d = lemma5d (encryptCharacter c (5 + n)) n
-- --   in transitivity≡Character 5d (substitute≡Character (λ c' → decryptCharacter c' n ≡Character c) (symmetry≡Character 5e) (characterDecryptionIsSound c n))

-- -- -- -- -- -- strings

-- -- -- -- -- data String : Set where
-- -- -- -- --   empty : String
-- -- -- -- --   _∷_ : Character → String → String
-- -- -- -- -- infixr 20 _∷_

-- -- -- -- -- infix 10 _≡String_
-- -- -- -- -- data _≡String_ (s : String) : String → Set where
-- -- -- -- --   refl : s ≡String s

-- -- -- -- -- _ : A ∷ B ∷ empty ≡String A ∷ B ∷ empty
-- -- -- -- -- _ = refl

-- -- -- -- -- encryptString
-- -- -- -- --   : String
-- -- -- -- --   → Naturalnumber
-- -- -- -- --   → String
-- -- -- -- -- encryptString empty _ = empty
-- -- -- -- -- encryptString (c ∷ s) n = encryptCharacter c n ∷ encryptString s n

-- -- -- -- -- decryptString
-- -- -- -- --   : String
-- -- -- -- --   → Naturalnumber
-- -- -- -- --   → String
-- -- -- -- -- decryptString empty _ = empty
-- -- -- -- -- decryptString (c ∷ s) n = decryptCharacter c n ∷ decryptString s n

-- -- -- -- -- _ : A ∷ B ∷ empty ≡String A ∷ C ∷ empty → ⊥
-- -- -- -- -- _ = λ ()

-- -- -- -- -- congruencyOfChar∷String
-- -- -- -- --   : ∀ c₁ c₂ s₁ s₂
-- -- -- -- --   → c₁ ≡Character c₂
-- -- -- -- --   → s₁ ≡String s₂
-- -- -- -- --   → c₁ ∷ s₁ ≡String c₂ ∷ s₂
-- -- -- -- -- congruencyOfChar∷String _ _ _ _ refl refl = refl

-- -- -- -- -- stringDecryptionIsSound :
-- -- -- -- --   ∀ s n
-- -- -- -- --   → decryptString (encryptString s n) n ≡String s
-- -- -- -- -- stringDecryptionIsSound empty n = refl
-- -- -- -- -- stringDecryptionIsSound (c ∷ s) n =
-- -- -- -- --   let charRefl = characterDecryptionIsSound c n
-- -- -- -- --       stringRefl = stringDecryptionIsSound s n
-- -- -- -- --   in congruencyOfChar∷String
-- -- -- -- --        (decryptCharacter (encryptCharacter c n) n)
-- -- -- -- --        c
-- -- -- -- --        (decryptString (encryptString s n) n)
-- -- -- -- --        s
-- -- -- -- --        charRefl
-- -- -- -- --        stringRefl
