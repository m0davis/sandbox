open import AgdaIssue-Snowflake-CheckLHS-Performance

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
