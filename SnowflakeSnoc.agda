--{-# OPTIONS --show-implicit #-}
{-# OPTIONS -vprofile:10 #-}
module SnowflakeSnoc where

open import Prelude
  renaming ( _==_ to _≟_
           ; List to 𝑳
           ; [] to ∅
           ; _∷_ to _∷ₗ_
           )
  using ( ⊥
        ; ¬_
        ; _≡_
        ; ⊤
        ; case_of_
        ; ⊥-elim
        ; refl
        ; ∃
        ; _,_
        ; _×_
        ; fst ; snd
        ; Dec
        ; yes
        ; no
        ; Eq
        ; flip
        ; sym
        ; _⊔_
        ; _<_
        ; _≥_
        )

open import Relation.Nullary.Decidable using ()

open import Agda.Builtin.Nat using (suc; _-_; _+_) renaming (Nat to ℕ)
open import Relation.Binary.PropositionalEquality using (subst)
open import Tactic.Reflection.Reright
open import Tactic.Nat.Prelude


private
  _≢_ : ∀ {a} {A : Set a} → A → A → Set a
  A ≢ B = ¬ A ≡ B

  infix 0 _↔_
  _↔_ : ∀ {a b} (l : Set a) (r : Set b) → Set (a ⊔ b)
  l ↔ r = (l → r) × (r → l)

data 𝕃 {𝑨} (𝐴 : Set 𝑨) : Set 𝑨
data _∉_ {𝑨} {𝐴 : Set 𝑨} (x : 𝐴) : 𝕃 𝐴 → Set 𝑨

data 𝕃 {𝑨} (𝐴 : Set 𝑨) where
  ∅ : 𝕃 𝐴
  ∷ : {x₀ : 𝐴} → {x₁s : 𝕃 𝐴} → x₀ ∉ x₁s → 𝕃 𝐴

data _∉_ {𝑨} {𝐴 : Set 𝑨} (𝔞 : 𝐴) where
  ∉∅ : 𝔞 ∉ ∅
  ∉∷ : ∀ {x₀} → 𝔞 ≢ x₀ → ∀ {x₁s} → 𝔞 ∉ x₁s → (x₀∉x₁s : x₀ ∉ x₁s) → 𝔞 ∉ (∷ x₀∉x₁s)

𝕃→𝑳 : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → 𝑳 𝐴
𝕃→𝑳 ∅ = ∅
𝕃→𝑳 (∷ {x} ∉∅) = x ∷ₗ ∅
𝕃→𝑳 (∷ {x₀} (∉∷ {x₁} x {x₂s} x3 x4)) = x₀ ∷ₗ x₁ ∷ₗ 𝕃→𝑳 x₂s

data _∈_ {𝑨} {𝐴 : Set 𝑨} (𝔞 : 𝐴) : 𝕃 𝐴 → Set 𝑨 where
  here : ∀ {x₀s} (𝔞∉x₀s : 𝔞 ∉ x₀s) → 𝔞 ∈ ∷ 𝔞∉x₀s
  there : ∀ {x₁s} → (𝔞∈x₁s : 𝔞 ∈ x₁s) → ∀ {x₀} → (x₀∉x₁s : x₀ ∉ x₁s)  → 𝔞 ∈ ∷ x₀∉x₁s

∉→∈→⊥ : ∀ {𝑨} {𝐴 : Set 𝑨} {𝔞} {xs : 𝕃 𝐴} → 𝔞 ∉ xs → 𝔞 ∈ xs → ⊥
∉→∈→⊥ ∉∅ ()
∉→∈→⊥ (∉∷ x₀≢x₀ _ _) (here _) = x₀≢x₀ refl
∉→∈→⊥ (∉∷ 𝔞≢x₀ 𝔞∉x₁s _) (there 𝔞∈x₁s x₀∉x₁s) = ∉→∈→⊥ 𝔞∉x₁s 𝔞∈x₁s

_∉?_ : ∀ {𝑨} {𝐴 : Set 𝑨} ⦃ _ : Eq 𝐴 ⦄ (𝔞 : 𝐴) (xs : 𝕃 𝐴) → Dec (𝔞 ∉ xs)
𝔞 ∉? ∅ = yes ∉∅
𝔞 ∉? ∷ {x₀} {x₁s} x₀∉x₁s with 𝔞 ≟ x₀
... | yes 𝔞≡x₀ rewrite 𝔞≡x₀ = no (flip ∉→∈→⊥ (here x₀∉x₁s))
... | no 𝔞≢x₀ with 𝔞 ∉? x₁s
... | yes 𝔞∉x₁s = yes (∉∷ 𝔞≢x₀ 𝔞∉x₁s x₀∉x₁s)
... | no ¬𝔞∉x₁s = no (λ {(∉∷ _ 𝔞∉x₁s _) → ¬𝔞∉x₁s 𝔞∉x₁s})

data _[_]=_ {𝑨} {𝐴 : Set 𝑨} : 𝕃 𝐴 → ℕ → 𝐴 → Set 𝑨 where
  here  : ∀ {𝔞 xs} (𝔞∉xs : 𝔞 ∉ xs) → ∷ 𝔞∉xs [ 0 ]= 𝔞
  there : ∀ {x₀ x₁s} (x₀∉x₁s : x₀ ∉ x₁s) {i 𝔞} (x₁s[i]=𝔞 : x₁s [ i ]= 𝔞) → ∷ x₀∉x₁s [ suc i ]= 𝔞
{-
remove : ∀ {𝑨} {𝐴 : Set 𝑨} {a : 𝐴} {L : 𝕃 𝐴} {n : ℕ} → L [ n ]= a → ∃ λ L/a → ∀ n' → (n' < n → ∀ a' → L [ n' ]= a' → L/a [ n' ]= a') × (n' ≥ n → ∀ a' → L [ suc n' ]= a' → L/a [ n' ]= a')
remove (here {xs = L₁} a∉L₁) = L₁ , (λ n' → (λ { (Prelude.diff _ ()) _ _ }) , (λ n'≥0 a' → λ { (there .a∉L₁ L₁[n']=a') → L₁[n']=a' }))
remove (there x₀∉x₁s x₁s[i]=a) with remove x₁s[i]=a
remove (there {x₀} {x₁s} x₀∉x₁s x₁s[i]=a) | x , y = {!!}

pick : ∀ {𝑨} {𝐴 : Set 𝑨} {a : 𝐴} {L : 𝕃 𝐴} → a ∈ L → ∃ λ L/a → ∀ x → (x ∈ L/a) ↔ (x ∈ L × x ≢ a)
pick {a = a} (here ∉∅) = ∅ , (λ x → (λ ()) , (λ { (x∈a , x≢a) → {!!} }))
pick (here (∉∷ x 𝔞∉x₀s₁ 𝔞∉x₀s)) = {!!}
pick (there {x₁s} a∈x₁s {x₀} x₀∉x₁s) = {!!} , {!!}
-}
data _≛_ {𝑨} {𝐴 : Set 𝑨} : 𝕃 𝐴 → 𝕃 𝐴 → Set 𝑨 where
  ∅ : ∅ ≛ ∅

[]=-thm₀ : ∀ {𝑨} {𝐴 : Set 𝑨} {L : 𝕃 𝐴} {n} {a} → L [ n ]= a → a ∉ L → ⊥
[]=-thm₀ (here 𝔞∉xs) (∉∷ x x₁ .𝔞∉xs) = x refl
[]=-thm₀ (there x₀∉x₁s x) (∉∷ x₁ x₂ .x₀∉x₁s) = []=-thm₀ x x₂


[]=-thm₁ : ∀ {𝑨} {𝐴 : Set 𝑨} {L : 𝕃 𝐴} {n₁ n₂ : ℕ} {a₁ a₂ : 𝐴} → L [ n₁ ]= a₁ → L [ n₂ ]= a₂ → n₁ ≡ n₂ ↔ a₁ ≡ a₂
[]=-thm₁ (here 𝔞∉xs) (here .𝔞∉xs) = (λ x → refl) , (λ x → refl)
[]=-thm₁ (here 𝔞∉xs) (there .𝔞∉xs x₁) = (λ ()) , λ a₁≡a₂ → (⊥-elim ([]=-thm₀ (subst _ (sym a₁≡a₂) x₁ ) 𝔞∉xs))
[]=-thm₁ {L = ∷ .a₂∉x₁s} (there {x₁s = x₁s} a₂∉x₁s {i} x₁s[i]=a₁) (here .a₂∉x₁s) = (λ ()) , (λ a₁≡a₂ → ⊥-elim ([]=-thm₀ (subst (x₁s [ i ]=_) a₁≡a₂ x₁s[i]=a₁) a₂∉x₁s))
[]=-thm₁ (there x₀∉x₁s x) (there .x₀∉x₁s x₁) = (λ ss → fst ([]=-thm₁ x x₁) (by ss)) , (λ x1=x2 → by (snd ([]=-thm₁ x x₁) x1=x2))

data ∅⊂_ {𝑨} {𝐴 : Set 𝑨} : 𝕃 𝐴 → Set 𝑨 where
  ∅⊂∷ : ∀ {x₀ x₁s} → (x₀∉x₁s : x₀ ∉ x₁s) → ∅⊂ ∷ x₀∉x₁s

∈→∅⊂ : ∀ {𝑨} {𝐴 : Set 𝑨} {𝔞 : 𝐴} {xs : 𝕃 𝐴} → 𝔞 ∈ xs → ∅⊂ xs
∈→∅⊂ (here 𝔞∉x₀s) = ∅⊂∷ 𝔞∉x₀s
∈→∅⊂ (there _ x₀∉x₁s) = ∅⊂∷ x₀∉x₁s

lastIndex : ∀ {𝑨} {𝐴 : Set 𝑨} {L : 𝕃 𝐴} (∅⊂L : ∅⊂ L) → ℕ
lastIndex (∅⊂∷ ∉∅) = 0
lastIndex (∅⊂∷ (∉∷ x x₀∉x₁s₁ x₀∉x₁s)) = suc (lastIndex (∅⊂∷ x₀∉x₁s))

length : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → ℕ
length ∅ = 0
length (∷ {x₁s = x₁s} _) = suc (length x₁s)

open import Data.Permutation renaming (_∷_ to _∷ₚ_)
open import Data.Fin hiding (_-_; _+_) -- renaming (_∷_ to _∷ᶠ_)

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

[a] = ∷ a∉∅
[ab] = ∷ a∉b
[ba] = ∷ b∉a
[abc] = ∷ a∉bc
[cab] = ∷ c∉ab
[cba] = ∷ c∉ba
[abcd] = ∷ a∉bcd
[dcab] = ∷ d∉cab
[dcba] = ∷ d∉cba

{-
abcd → dcab

permutation
  3 ∷ (2 ∷ (0 ∷ []))
-}
import Prelude.Fin

perm₀ : Permutation 0
perm₀ = []

perm₁ : Permutation 1
perm₁ = zero ∷ₚ [] -- fromℕ 0 ∷ₚ []

perm₂ : Permutation 2
perm₂ = # 0 ∷ₚ # 0 ∷ₚ [] -- fromℕ 0 ∷ₚ []

perm : Permutation 4
perm = # 3 ∷ₚ # 2 ∷ₚ # 0 ∷ₚ # 0 ∷ₚ []

head : ∀ {𝑨} {𝐴 : Set 𝑨} {L} → ∅⊂ L → 𝐴
head (∅⊂∷ {x₀} _) = x₀

tail : ∀ {𝑨} {𝐴 : Set 𝑨} {L} → ∅⊂ L → 𝕃 𝐴
tail (∅⊂∷ {x₁s = x₁s} _) = x₁s

last : ∀ {𝑨} {𝐴 : Set 𝑨} {L} → ∅⊂ L → 𝐴
last (∅⊂∷ {x₀} {∅} _) = x₀
last (∅⊂∷ {x₁s = ∷ x₁∉x₂s} _) = last (∅⊂∷ x₁∉x₂s)

last-thm₁ : ∀ {𝑨} {𝐴 : Set 𝑨} {L : 𝕃 𝐴} → (∅⊂L : ∅⊂ L) → L [ lastIndex ∅⊂L ]= last ∅⊂L
last-thm₁ (∅⊂∷ ∉∅) = here ∉∅
last-thm₁ (∅⊂∷ (∉∷ x x₀∉x₁s₁ x₀∉x₁s)) = there (∉∷ x x₀∉x₁s₁ x₀∉x₁s) (last-thm₁ (∅⊂∷ x₀∉x₁s))

tail∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {𝔞} {xs : 𝕃 𝐴} (∅⊂xs : ∅⊂ xs) → 𝔞 ∉ xs → 𝔞 ∉ tail ∅⊂xs
tail∉ () ∉∅
tail∉ (∅⊂∷ x) (∉∷ x₁ ∉∅ .x) = ∉∅
tail∉ (∅⊂∷ x) (∉∷ x₃ (∉∷ x₄ x₅ x₂) .x) = ∉∷ x₄ x₅ x₂
{-
¬∈→∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {𝔞} {xs : 𝕃 𝐴} → (𝔞 ∈ xs → ⊥) → 𝔞 ∉ xs
¬∈→∉ {𝔞 = 𝔞} {xs = ∅} ¬𝔞∈xs = ∉∅
¬∈→∉ {𝔞 = 𝔞} {xs = ∷ {x₀} {x₁s = ∅} x₀∉∅} ¬𝔞∈xs = ∉∷ (λ 𝔞≡x₀ → ⊥-elim (¬𝔞∈xs (subst (_∈ ∷ _) (sym 𝔞≡x₀) (here _)))) ∉∅ x₀∉∅
¬∈→∉ {xs = ∷ (∉∷ x ∉∅ ∉∅)} ¬𝔞∈xs = {!!}
¬∈→∉ {xs = ∷ (∉∷ x₄ (∉∷ x₅ x₀∉x₁∉x₂s .x) (∉∷ x₂ x₁∉x₂s x))} ¬𝔞∈xs = {!!}

¬∈→∉'' : ∀ {𝑨} {𝐴 : Set 𝑨} ⦃ _ : Eq 𝐴 ⦄ {𝔞} {xs : 𝕃 𝐴} → (𝔞 ∈ xs → ⊥) → 𝔞 ∉ xs
¬∈→∉'' {𝔞 = 𝔞} {xs = ∅} ¬𝔞∈xs = ∉∅
¬∈→∉'' {𝔞 = 𝔞} {xs = ∷ {x₀} {x₁s = ∅} x₀∉∅} ¬𝔞∈xs = ∉∷ (λ 𝔞≡x₀ → ⊥-elim (¬𝔞∈xs (subst (_∈ ∷ _) (sym 𝔞≡x₀) (here _)))) ∉∅ x₀∉∅
¬∈→∉'' {𝔞 = 𝔞} {xs = ∷ {x₀} {x₁s = ∷ {x₁} {x₂s} x₁∉x₂s} x₀∉x₁∉x₂s} ¬𝔞∈xs with 𝔞 ≟ x₀
... | yes 𝔞≡x₀ = ⊥-elim (¬𝔞∈xs (subst (_∈ ∷ x₀∉x₁∉x₂s) (sym 𝔞≡x₀) (here _)))
... | no 𝔞≢x₀ = {!∉→∈→⊥ x₀∉x₁∉x₂s!}

¬∈→∉' : ∀ {𝑨} {𝐴 : Set 𝑨} {𝔞} {xs : 𝕃 𝐴} → (𝔞 ∈ xs → ⊥) → 𝔞 ∉ xs
¬∈→∉' {𝔞 = 𝔞} {xs = ∅} ¬𝔞∈xs = ∉∅
¬∈→∉' {𝔞 = 𝔞} {xs = ∷ {x₀} {x₁s = ∅} x₀∉∅} ¬𝔞∈xs = ∉∷ (λ 𝔞≡x₀ → ⊥-elim (¬𝔞∈xs (subst (_∈ ∷ _) (sym 𝔞≡x₀) (here _)))) ∉∅ x₀∉∅
¬∈→∉' {𝔞 = 𝔞} {xs = ∷ {x₀} {x₁s = ∷ {x₁} {x₂s} x₁∉x₂s} x₀∉x₁∉x₂s} ¬𝔞∈xs = ∉∷ (λ 𝔞≡x₀ → ⊥-elim (¬𝔞∈xs ((subst (_∈ ∷ _) (sym 𝔞≡x₀) (here _))))) (tail∉ (∅⊂∷ x₀∉x₁∉x₂s) (∉∷ (λ 𝔞≡x₀ → ⊥-elim (¬𝔞∈xs (subst (_∈ ∷ _) (sym 𝔞≡x₀) (here _)))) {!!} x₀∉x₁∉x₂s)) x₀∉x₁∉x₂s
-}
mutual
  init : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀s : 𝕃 𝐴} (∅⊂x₀s : ∅⊂ x₀s) → 𝕃 𝐴
  init (∅⊂∷ ∉∅) = ∅
  init (∅⊂∷ (∉∷ _ x₀∉x₂s x₁∉x₂s)) = ∷ (init∉ (∅⊂∷ _) (∉∷ _ x₀∉x₂s x₁∉x₂s))

  init∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀ : 𝐴} {x₁s : 𝕃 𝐴} (∅⊂x₁s : ∅⊂ x₁s) → x₀ ∉ x₁s → x₀ ∉ init ∅⊂x₁s
  init∉ () ∉∅
  init∉ (∅⊂∷ _) (∉∷ _ ∉∅ ∉∅) = ∉∅
  init∉ (∅⊂∷ _) (∉∷ x₀≢x₁ (∉∷ x₀≢x₂ x₀∉x₃s x₂∉x₃s) (∉∷ x₁≢x₂ x₁∉x₃s .x₂∉x₃s)) = ∉∷ x₀≢x₁ (init∉ _ (∉∷ x₀≢x₂ x₀∉x₃s x₂∉x₃s)) (init∉ _ (∉∷ x₁≢x₂ x₁∉x₃s x₂∉x₃s))

shiftRight : ∀ {𝑨} {𝐴 : Set 𝑨} {xs : 𝕃 𝐴} (∅⊂xs : ∅⊂ xs) → last ∅⊂xs ∉ init ∅⊂xs
shiftRight (∅⊂∷ ∉∅) = ∉∅
shiftRight (∅⊂∷ {x₀} (∉∷ {x₁} x₀≢x₁ {x₂s} x₀∉x₂s x₁∉x₂s)) =
  ∉∷ (let x₁s[last]=lastx₁s = last-thm₁ (∅⊂∷ x₁∉x₂s) in
          λ lastx₁s≡x₀ →
                       let x₀≡lastx₁s = sym lastx₁s≡x₀
                       in let x₁s[last]=x₀ = subst (∷ x₁∉x₂s [ lastIndex (∅⊂∷ x₁∉x₂s) ]=_) lastx₁s≡x₀ x₁s[last]=lastx₁s --reright lastx₁s≡x₀ x₁s[last]=lastx₁s
                       in []=-thm₀ x₁s[last]=x₀ (∉∷ x₀≢x₁ x₀∉x₂s x₁∉x₂s) )
     (shiftRight (∅⊂∷ x₁∉x₂s))
     (init∉ (∅⊂∷ x₁∉x₂s) (∉∷ x₀≢x₁ x₀∉x₂s x₁∉x₂s))

last-thm : last (∅⊂∷ a∉b) ≡ ⋆b
last-thm = refl

init-thm : init (∅⊂∷ a∉b) ≡ [a]
init-thm = refl
{-
lemma : (bnotina : ⋆b ∉ [a]) → bnotina ≡ b∉a
lemma (∉∷ x ∉∅ .∉∅) = {!!}

sr-lem1 : ∀ {eq : ⋆b ≡ ⋆a} → (t : Set) → t ≡ ⊥ -- a≢b (sym eq)
sr-lem1 = {!!}

sr-lem : ∀ {eq} → []=-thm₀ (subst (_[_]=_ (∷ ∉∅) 0) eq (here ∉∅)) (∉∷ a≢b ∉∅ ∉∅) ≡ a≢b (sym eq)
sr-lem {eq} = {!!}

sr-thm : shiftRight (∅⊂∷ a∉b) ≡ b∉a
sr-thm = {!!}

sr-law : 𝕃→𝑳 (∷ (shiftRight (∅⊂∷ a∉b))) ≡ 𝕃→𝑳 (∷ b∉a)
sr-law = {!refl!}
-}
{-
shiftRight∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {xs : 𝕃 𝐴} (∅⊂xs : ∅⊂ xs) {𝔞 : 𝐴} → 𝔞 ∉ xs → 𝔞 ∉ ∷ (shiftRight ∅⊂xs)
shiftRight∉ (∅⊂∷ ∉∅) (∉∷ 𝔞≢x₀ 𝔞∉x₁s .∉∅) = ∉∷ 𝔞≢x₀ 𝔞∉x₁s ∉∅
shiftRight∉ (∅⊂∷ (∉∷ x x₀∉x₁s₁ x₀∉x₁s)) (∉∷ 𝔞≢x₀ 𝔞∉x₁s .(∉∷ x x₀∉x₁s₁ x₀∉x₁s)) = {!!}
-}
rotateRight : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → 𝕃 𝐴
rotateRight ∅ = ∅
rotateRight (∷ {x₀} ∉∅) = ∷ {x₀ = x₀} ∉∅
rotateRight (∷ x₀∉x₁s) = ∷ (shiftRight (∅⊂∷ x₀∉x₁s))


transpose-1st-two : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀ : 𝐴} {x₁s : 𝕃 𝐴} (∅⊂x₁s : ∅⊂ x₁s) (x₀∉x₁s : x₀ ∉ x₁s) → 𝕃 𝐴
transpose-1st-two (∅⊂∷ x₁∉x₂s) (∉∷ x₀≢x₁ x₀∉x₂s .x₁∉x₂s) = ∷ (∉∷ ((sym' x₀≢x₁)) x₁∉x₂s x₀∉x₂s)

transposeFirst : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → 𝕃 𝐴
transposeFirst ∅ = ∅
transposeFirst (∷ {x₀} ∉∅) = ∷ {x₀ = x₀} ∉∅
transposeFirst (∷ {x₀} (∉∷ x₀≢x₁ x₀∉x₂s x₁∉x₂s)) = ∷ (∉∷ (sym' x₀≢x₁) x₁∉x₂s x₀∉x₂s)

rotateRightBy : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
rotateRightBy 0 x = x
rotateRightBy (suc n) x = rotateRightBy n (rotateRight x)

moveNthFromEndLeft : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
moveNthFromEndLeft _ ∅ = ∅
moveNthFromEndLeft _ (∷ {x₀} ∉∅) = ∷ {x₀ = x₀} ∉∅
moveNthFromEndLeft n xs = rotateRightBy (length xs - 2 - n) (transposeFirst (rotateRightBy (2 + n) xs))

moveEndLeftBy : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
moveEndLeftBy _ ∅ = ∅
moveEndLeftBy _ (∷ {x₀} ∉∅) = ∷ {x₀ = x₀} ∉∅
moveEndLeftBy 0 xs = xs
moveEndLeftBy (suc n) xs = moveNthFromEndLeft n (moveEndLeftBy n xs)

moveNthFromBeginningLeftBy : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → ℕ → 𝕃 𝐴 → 𝕃 𝐴
moveNthFromBeginningLeftBy _ 0 xs = xs
moveNthFromBeginningLeftBy n m xs with length xs
... | l with suc n ≟ l
... | yes _ =                       (moveEndLeftBy m (                           xs))
... | no _  = rotateRightBy (suc n) (moveEndLeftBy m (rotateRightBy (l -(suc n)) xs))

-- bacd
-- bcad
-- 2 1
--

-- bacd rotateRight 1
-- dbac
-- dbca
-- bcad


-- bacd rotateRight 3
-- acdb
-- acbd
-- dacb

open import Agda.Builtin.List

permToList : ∀ {n} → Permutation n → List ℕ
permToList [] = []
permToList (x ∷ₚ x₁) = _∷_ (toℕ x) (permToList x₁)

reorder : ∀ {𝑨} {𝐴 : Set 𝑨} (L : 𝕃 𝐴) → Permutation (length L) → 𝕃 𝐴
reorder xs perm = go 0 (permToList perm) xs where
  go : ∀ {𝑨} {𝐴 : Set 𝑨} → (n : ℕ) → List ℕ → (L : 𝕃 𝐴) → 𝕃 𝐴
  go _ _ ∅ = ∅
  go _ [] xs = xs
  go n (p₀ ∷ₗ ps) xs = go (suc n) ps (moveNthFromBeginningLeftBy (n + p₀) p₀ xs)

-- abcd 0 1100
-- bacd 1 100
-- bcad 2 00
-- bcad 3 0
-- bcad 4

rotate-thm : 𝕃→𝑳 (rotateRight [ab]) ≡ 𝕃→𝑳 [ba] -- reorder [abcd] perm ≡ [dcab]
rotate-thm = refl

reorder-thm₂ : 𝕃→𝑳 (reorder [ab] (# 1 ∷ₚ # 0 ∷ₚ [])) ≡ 𝕃→𝑳 [ba]
reorder-thm₂ = refl

reorder-thm₃' : 𝕃→𝑳 (reorder [abc] (# 2 ∷ₚ # 0 ∷ₚ # 0 ∷ₚ [])) ≡ 𝕃→𝑳 [cab]
reorder-thm₃' = refl

reversePerm : ∀ {n : ℕ} → Permutation n
reversePerm {0} = []
reversePerm {suc n} = fromℕ n ∷ₚ reversePerm

reverse : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → 𝕃 𝐴
reverse x = reorder x reversePerm









--reorder-thm₃ : 𝕃→𝑳 (reorder [abc] (# 2 ∷ₚ # 1 ∷ₚ # 0 ∷ₚ [])) ≡ 𝕃→𝑳 [cba]
--reorder-thm₃ = refl

reorder-thm₄ : 𝕃→𝑳 (reorder [abcd] (# 3 ∷ₚ # 2 ∷ₚ # 1 ∷ₚ # 0 ∷ₚ [])) ≡ 𝕃→𝑳 [dcba]
reorder-thm₄ = refl



--reverse-thm₃ : 𝕃→𝑳 (reorder [abc] (# 2 ∷ₚ # 1 ∷ₚ # 0 ∷ₚ [])) ≡ 𝕃→𝑳 (reverse [abc])
--reverse-thm₃ = refl

--reverse-thm₄ : 𝕃→𝑳 (reorder [abcd] (# 3 ∷ₚ # 2 ∷ₚ # 1 ∷ₚ # 0 ∷ₚ [])) ≡ 𝕃→𝑳 (reverse [abcd])
--reverse-thm₄ = refl



















-- {-
-- reverse-thm₁ : 𝕃→𝑳 (reorder [ab] (# 1 ∷ₚ # 0 ∷ₚ [])) ≡ 𝕃→𝑳 (reverse [ab])
-- reverse-thm₁ = {!refl!}
-- -}
-- {-
-- reverse-thm₂ : 𝕃→𝑳 (reorder [abc] (# 2 ∷ₚ # 1 ∷ₚ # 0 ∷ₚ [])) ≡ 𝕃→𝑳 (reverse [abc])
-- reverse-thm₂ = {!refl!}
-- -}
-- {-
-- reverse-thm : 𝕃→𝑳 (reorder [abcd] (# 3 ∷ₚ # 2 ∷ₚ # 1 ∷ₚ # 0 ∷ₚ [])) ≡ 𝕃→𝑳 (reverse [abcd])
-- reverse-thm = refl
-- -}

-- open import Data.Nat.Base
-- open import Relation.Nullary renaming (Dec to DEC; yes to YES; no to NO)


-- {-
-- reversePerm : ∀ {n} → Permutation n
-- reversePerm {0} = []
-- reversePerm {suc 0} = (# 0) ∷ₚ reversePerm
-- reversePerm {suc (suc n)} = (#_ ((suc n)) {n = suc (suc n)} {m<n = {!!}}) ∷ₚ reversePerm
-- -- Goal: Relation.Nullary.Decidable.True
-- --       (suc (suc n) .Data.Nat.Base.≤? suc (suc n)
-- --        | (suc n .Data.Nat.Base.≤? suc n | n .Data.Nat.Base.≤? n))
-- -}
-- {-
-- perminv : Set
-- perminv = {!reversePerm {4}!}
-- -}
-- -- bca
-- -- cab
-- -- bcda
-- -- dabc

-- data ⌜_∩_≡∅⌝ {𝑨} {𝐴 : Set 𝑨} : 𝕃 𝐴 → 𝕃 𝐴 → Set 𝑨 where
--   ε : ∀ {y₀s} → ⌜ ∅ ∩ y₀s ≡∅⌝
--   φ : ∀ {x₀s y₀s} → (∅⊂x₀s : ∅⊂ x₀s) → (x₀∉y₀s : head ∅⊂x₀s ∉ y₀s) →  ⌜ tail ∅⊂x₀s ∩ ∷ x₀∉y₀s ≡∅⌝ → ⌜ x₀s ∩ y₀s ≡∅⌝

-- take : ∀ {𝑨} {𝐴 : Set 𝑨} → ℕ → 𝕃 𝐴 → 𝕃 𝐴
-- take 0 _ = ∅
-- take (suc n) ∅ = ∅
-- take (suc n) (∷ {x₁s = ∅} x₀∉∅) = ∅
-- take (suc n) (∷ {x₀} {x₁s = ∷ x₁∉x₂s} x₀∉x₁s) = ∷ (init∉ (∅⊂∷ (x₁∉x₂s)) x₀∉x₁s)

-- mutual
--   append : ∀ {𝑨} {𝐴 : Set 𝑨} {𝔞 : 𝐴} {xs : 𝕃 𝐴} (𝔞∉xs : 𝔞 ∉ xs) → 𝕃 𝐴
--   append {𝔞 = 𝔞} {∅} ∉∅ = ∷ {x₀ = 𝔞} ∉∅
--   append {𝔞 = 𝔞} {∷ {x₀} x₀∉x₁s} (∉∷ 𝔞≢x₀ {x₁s} 𝔞∉x₁s .x₀∉x₁s) = ∷ {x₀ = x₀} {x₁s = append 𝔞∉x₁s} (append∉ 𝔞≢x₀ 𝔞∉x₁s x₀∉x₁s)

--   append∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {𝔞 x₀ : 𝐴} (𝔞≢x₀ : 𝔞 ≢ x₀) {x₁s : 𝕃 𝐴} (𝔞∉x₁s : 𝔞 ∉ x₁s) (x₀∉x₁s : x₀ ∉ x₁s) → x₀ ∉ append 𝔞∉x₁s
--   append∉ 𝔞≢x₀ ∉∅ ∉∅ = ∉∷ (λ x₀≢𝔞 → 𝔞≢x₀ (sym x₀≢𝔞)) ∉∅ ∉∅
--   append∉ 𝔞≢x₀ (∉∷ 𝔞≢x₁ 𝔞∉x₂s x₁∉x₂s) (∉∷ x₀≢x₁ x₀∉x₂s .x₁∉x₂s) = ∉∷ x₀≢x₁ (append∉ 𝔞≢x₀ 𝔞∉x₂s x₀∉x₂s) (append∉ 𝔞≢x₁ 𝔞∉x₂s x₁∉x₂s)
-- {-
-- mutual
--   reverse : ∀ {𝑨} {𝐴 : Set 𝑨} → 𝕃 𝐴 → 𝕃 𝐴
--   reverse ∅ = ∅
--   reverse (∷ {x₁s = ∅} x₀∉∅) = ∷ x₀∉∅
--   reverse (∷ {x₀ = x₀} {x₁s = ∷ x₁∉x₂s} x₀∉x₁s) = append (reverse∉ x₀∉x₁s) -- {!shiftRight (reverse tail (∅⊂∷ x₀∉x₁s)!} --

--   reverse∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {𝔞 : 𝐴} {xs : 𝕃 𝐴} (𝔞∉xs : 𝔞 ∉ xs) → 𝔞 ∉ reverse xs
--   reverse∉ ∉∅ = ∉∅
--   reverse∉ (∉∷ x ∉∅ ∉∅) = ∉∷ x ∉∅ ∉∅
--   reverse∉ (∉∷ x₂ (∉∷ x₃ ∉∅ ∉∅) (∉∷ x ∉∅ .∉∅)) = ∉∷ x₃ (∉∷ x₂ ∉∅ ∉∅) (∉∷ (λ z → x (sym z)) ∉∅ ∉∅)
--   reverse∉ (∉∷ x₃ (∉∷ x₄ (∉∷ x₅ 𝔞∉xs₃ 𝔞∉xs₂) 𝔞∉xs) (∉∷ x 𝔞∉xs₁ .𝔞∉xs)) = {!𝔞∉xs₃!}
-- {-
--   reverse∉ ∉∅ = ∉∅
--   reverse∉ (∉∷ x 𝔞∉xs₁ ∉∅) = ∉∷ x 𝔞∉xs₁ ∉∅
--   reverse∉ {𝔞 = 𝔞} (∉∷ {x₀} 𝔞≢x₀ (∉∷ {x₁} 𝔞≢x₁ 𝔞∉x₂s x₁∉x₂s) (∉∷ {.x₁} x₀≢x₁ x₀∉x₂s .x₁∉x₂s)) = {!!}
-- -}
-- -}

-- {-

-- shiftLeft abcd → b∉cda

-- abcd → d∉abc

-- abc → c∉ab

-- ab → b∉a


-- bcda

-- dabc

-- abcd

-- cba

-- adcb


-- adcb

-- equivalent bcd dcb → x ∉ bcd → x ∉ dcb

-- reverse∉ :

-- shiftRight∉ : a ∉ bcd → d ∉ abc

-- shiftRight∉ b∉c = c∉b

-- shiftRight∉ a∉bc = c∉ba

-- abc
-- a∉bc
-- c∉ab



-- c∉ba

-- d∉abc : last abcd ∉ init abcd
-- dabc : ∷ d∉abc

-- a ∉ bcd

-- ∷ d∉bc



-- ∀ {𝑨} {𝐴 : Set 𝑨} {a : 𝐴} {bcd : 𝕃 𝐴} (a∉bcd : a ∉ bcd) (a∉cb : a ∉ (reverse (init bcd))) → last bcd ∉ append a∉cb

-- ∀ {𝑨} {𝐴 : Set 𝑨} {a : 𝐴} {bcd : 𝕃 𝐴} (a∉bcd : a ∉ bcd) → (a∉cb : a ∉ (reverse (init bcd)))

-- shiftRight ab = b∉a
-- ∷ (shiftRight ab) = ba

-- ∷ (shiftRight bc) = cb

-- shiftRight bc = c∉b



-- shiftRight abc = c∉ab

-- shiftRight abcd = d∉abc

-- d∉abc      = ∉∷ {a} d≢a {bc} d∉bc a∉bc

-- bc = ∷ {b} {c} b∉c
-- a  = ∷ {a} {∅} a∉∅

-- d∉bc = ∉∷ {b} d≢b {c} d∉c b∉c
-- a∉bc = ∉∷ {b} a≢b {c} a∉c b∉c



-- abcd       = ∷ {a} {bcd} a∉bcd
-- bcd        = ∷ {b} {cd}  b∉cd
-- cd         = ∷ {c} {d}   c∉d
-- d          = ∷ {d} {∅}   d∉∅

-- a∉bcd       = ∉∷ {b} a≢b {cd} a∉cd b∉cd

-- a∉cd       = ∉∷ {c} a≢c {d} a∉d c∉d
-- b∉cd       = ∉∷ {c} b≢c {d} b∉d c∉d

-- a∉d        = ∉∷ [d} a≢d {∅} a∉∅ d∉∅
-- b∉d        = ∉∷ {d} b≢d {∅} b∉∅ d∉∅
-- c∉d        = ∉∷ {d} c≢d {∅} c∉∅ d∉∅

-- a∉∅        = ∉∅
-- b∉∅        = ∉∅
-- c∉∅        = ∉∅
-- d∉∅        = ∉∅




-- dcba       = ∷ {d} {cba} d∉cba
-- cba        = ∷ {c} {ba}  c∉ba
-- ba         = ∷ {b} {a}   b∉a
-- a          = ∷ {a} {∅}   a∉∅

-- d∉cba      = ∉∷ {c} d≢c {ba} d∉ba c∉ba

-- d∉ba       = ∉∷ {b} d≢b {a} d∉a b∉a
-- c∉ba       = ∉∷ {b} c≢b {a} c∉a b∉a

-- d∉a        = ∉∷ [a} d≢a {∅} d∉∅ a∉∅
-- c∉a        = ∉∷ {a} c≢a {∅} c∉∅ a∉∅
-- b∉a        = ∉∷ {a} b≢a {∅} b∉∅ a∉∅

-- d∉∅        = ∉∅
-- c∉∅        = ∉∅
-- b∉∅        = ∉∅
-- a∉∅        = ∉∅










-- a          = ∷ {a} {∅} a∉∅
-- ba         = ∷ {b} {a} b∉a
-- cba        = ∷ {c} {ba} c∉ba

-- c∉ba       = ∉∷ {b} c≢b {a} c∉a b∉a

-- c∉a        = ∉∷ {a} c≢a {∅} c∉∅ a∉∅
-- b∉a        = ∉∷ {a} b≢a {∅} b∉∅ a∉∅

-- a∉∅        = ∉∅
-- b∉∅        = ∉∅
-- c∉∅        = ∉∅













-- abc        = ∷ {a} {bc} a∉bc
-- bc         = ∷ {b} {c} b∉c
-- c          = ∷ {c} {∅} c∉∅

-- a∉bc       = ∉∷ {b} a≢b {c} a∉c b∉c

-- b∉c        = ∉∷ {c} b≢c {∅} b∉∅ c∉∅
-- a∉c        = ∉∷ [c} a≢c {∅} a∉∅ c∉∅

-- a∉∅        = ∉∅
-- b∉∅        = ∉∅
-- c∉∅        = ∉∅


-- a          = ∷ {a} {∅} a∉∅
-- ba         = ∷ {b} {a} b∉a
-- cba        = ∷ {c} {ba} c∉ba

-- c∉ba       = ∉∷ {b} c≢b {a} c∉a b∉a

-- c∉a        = ∉∷ {a} c≢a {∅} c∉∅ a∉∅
-- b∉a        = ∉∷ {a} b≢a {∅} b∉∅ a∉∅

-- a∉∅        = ∉∅
-- b∉∅        = ∉∅
-- c∉∅        = ∉∅

-- data 𝕃 {𝑨} (𝐴 : Set 𝑨) where
--   ∅ : 𝕃 𝐴
--   ∷ : {x₀ : 𝐴} → {x₁s : 𝕃 𝐴} → x₀ ∉ x₁s → 𝕃 𝐴

-- data _∉_ {𝑨} {𝐴 : Set 𝑨} (𝔞 : 𝐴) where
--   ∉∅ : 𝔞 ∉ ∅
--   ∉∷ : ∀ {x₀} → 𝔞 ≢ x₀ → ∀ {x₁s} → 𝔞 ∉ x₁s → (x₀∉x₁s : x₀ ∉ x₁s) → 𝔞 ∉ (∷ x₀∉x₁s)
-- -}


-- -- ∪ : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀s y₀s} → ⌜ x₀s ∩ y₀s ≡∅⌝ → 𝕃 𝐴
-- -- ∪ = {!!} where
-- --   ∪ʳ : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀s y₀s} → ⌜ x₀s ∩ y₀s ≡∅⌝ → 𝕃 𝐴
-- --   ∪ʳ (ε {y₀s}) = y₀s
-- --   ∪ʳ (φ {x₀s} {y₀s} ∅⊂x₀s x₀∉y₀s x₁s∩x₀y₀s≡∅) = ∪ʳ x₁s∩x₀y₀s≡∅


-- -- -- data ⌜_∩_≡∅⌝ {𝑨} {𝐴 : Set 𝑨} : 𝕃 𝐴 → 𝕃 𝐴 → Set 𝑨 where
-- -- --   ∅∩⋆ : ∀ {y₀s} → ⌜ ∅ ∩ y₀s ≡∅⌝
-- -- --   ⋆∩∅ : ∀ {x₀s} → ⌜ x₀s ∩ ∅ ≡∅⌝
-- -- --   ←∩← : ∀ {x₀s y₀s} → (∅⊂x₀s : ∅⊂ x₀s) → (x₀∉y₀s : head ∅⊂x₀s ∉ y₀s) →  ⌜ tail ∅⊂x₀s ∩ ∷ x₀∉y₀s ≡∅⌝ → ⌜ x₀s ∩ y₀s ≡∅⌝
-- -- --   →∩→ : ∀ {x₀s y₀s} → (∅⊂y₀s : ∅⊂ y₀s) → (y₀∉x₀s : head ∅⊂y₀s ∉ x₀s) →  ⌜ ∷ y₀∉x₀s ∩ tail ∅⊂y₀s ≡∅⌝ → ⌜ x₀s ∩ y₀s ≡∅⌝

-- -- -- ∩-assoc : ∀ {𝑨} {𝐴 : Set 𝑨} → {x y : 𝕃 𝐴} → ⌜ x ∩ y ≡∅⌝ → ⌜ y ∩ x ≡∅⌝
-- -- -- ∩-assoc ∅∩⋆ = ⋆∩∅
-- -- -- ∩-assoc ⋆∩∅ = ∅∩⋆
-- -- -- ∩-assoc (←∩← ∅⊂x₀s x₀∉y₀s x₁) = →∩→ ∅⊂x₀s x₀∉y₀s (∩-assoc x₁)
-- -- -- ∩-assoc (→∩→ ∅⊂y₀s y₀∉x₀s x₁) = ←∩← ∅⊂y₀s y₀∉x₀s (∩-assoc x₁)

-- -- -- ∪ : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀s y₀s : 𝕃 𝐴} → ⌜ x₀s ∩ y₀s ≡∅⌝ → 𝕃 𝐴
-- -- -- ∪ (∅∩⋆ {y₀s}) = y₀s
-- -- -- ∪ (⋆∩∅ {x₀s}) = x₀s
-- -- -- ∪ (←∩← ∅⊂x₀s x₀∉y₀s x) = ∪ x
-- -- -- ∪ (→∩→ ∅⊂y₀s y₀∉x₀s x) = ∪ x

-- -- -- make-∅∩⋆ : ∀ {𝑨} {𝐴 : Set 𝑨} (⋆ : 𝕃 𝐴) → ⌜ ∅ ∩ ⋆ ≡∅⌝
-- -- -- make-∅∩⋆ ⋆ = ∅∩⋆ {y₀s = ⋆}

-- -- -- make-⋆∩∅ : ∀ {𝑨} {𝐴 : Set 𝑨} (⋆ : 𝕃 𝐴) → ⌜ ⋆ ∩ ∅ ≡∅⌝
-- -- -- make-⋆∩∅ ⋆ = ⋆∩∅ {x₀s = ⋆}

-- -- -- reverse : ∀ {𝑨} {𝐴 : Set 𝑨} → {⋆ : 𝕃 𝐴} → ⌜ ∅ ∩ ⋆ ≡∅⌝ → ⌜ ⋆ ∩ ∅ ≡∅⌝
-- -- -- reverse ∅∩⋆ = ⋆∩∅
-- -- -- reverse ⋆∩∅ = ∅∩⋆
-- -- -- reverse (←∩← ∅⊂x₀s x₀∉y₀s x) = ⋆∩∅
-- -- -- reverse (→∩→ ∅⊂y₀s y₀∉x₀s x) = ⋆∩∅

-- -- -- -- data ⌜_∩_≡∅⌝ {𝑨} {𝐴 : Set 𝑨} : 𝕃 𝐴 → 𝕃 𝐴 → Set 𝑨 where
-- -- -- --   ε : ∀ {y₀s} → ⌜ ∅ ∩ y₀s ≡∅⌝
-- -- -- --   φ : ∀ {x₀s y₀s} → (∅⊂x₀s : ∅⊂ x₀s) → (x₀∉y₀s : head ∅⊂x₀s ∉ y₀s) →  ⌜ tail ∅⊂x₀s ∩ ∷ x₀∉y₀s ≡∅⌝ → ⌜ x₀s ∩ y₀s ≡∅⌝
-- -- -- -- -- φ (abc ∩ def) → dabc ∩ ef

-- -- -- -- -- φ (bc ∩ adef)  → abc ∩ def
-- -- -- -- -- φ (c ∩ badef)  → bc ∩ adef
-- -- -- -- -- φ (∅ ∩ cbadef) → c ∩ badef
-- -- -- -- -- ε              → ∅ ∩ cbadef

-- -- -- -- data ⌜_∩′_≡∅⌝ {𝑨} {𝐴 : Set 𝑨} : 𝕃 𝐴 → 𝕃 𝐴 → Set 𝑨 where
-- -- -- --   ε : ∀ {x₀s} → ⌜ x₀s ∩′ ∅ ≡∅⌝
-- -- -- --   φ : ∀ {x₀s y₀s} → (∅⊂y₀s : ∅⊂ y₀s) → (y₀∉x₀s : head ∅⊂y₀s ∉ x₀s) →  ⌜ ∷ y₀∉x₀s ∩′ tail ∅⊂y₀s ≡∅⌝ → ⌜ x₀s ∩′ y₀s ≡∅⌝
-- -- -- -- -- φ (abc ∩ def) → bc ∩ adef

-- -- -- -- -- φ (dabc ∩ ef)  → abc ∩ def
-- -- -- -- -- φ (edabc ∩ f)  → dabc ∩ ef
-- -- -- -- -- φ (fedabc ∩ ∅) → edabc ∩ f
-- -- -- -- -- ε              → fedabc ∩ ∅

-- -- -- -- head' : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀} {x₁s : 𝕃 𝐴} → x₀ ∉ x₁s → ⌜ x₁s ∩ ∷ {x₀ = x₀} ∉∅ ≡∅⌝
-- -- -- -- head' ∉∅ = ε
-- -- -- -- head' {x₀ = x₀} (∉∷ {x₁} x₀≢x₁ {x₂s} x₀∉x₂s x₁∉x₂s) = φ (∅⊂∷ x₁∉x₂s) (∉∷ (λ x₁≡x₀ → x₀≢x₁ (sym x₁≡x₀)) ∉∅ ∉∅) {!head' x₀∉x₂s!}

-- -- -- -- mutual
-- -- -- --   ∩′→∩ : ∀ {𝑨} {𝐴 : Set 𝑨} → {x y : 𝕃 𝐴} → ⌜ x ∩′ y ≡∅⌝ → ⌜ x ∩ y ≡∅⌝
-- -- -- --   ∩′→∩ {x = ∅} ε = ε
-- -- -- --   ∩′→∩ {x = ∷ {x₀} {x₁s} x₀∉x₁s} ε = φ (∅⊂∷ x₀∉x₁s) ∉∅ (head' x₀∉x₁s)
-- -- -- --   ∩′→∩ (φ ∅⊂y₀s y₀∉x₀s y₀x₀s∩′y₁s) = {!y₀x₀s∩′y₁s!}

-- -- -- --   ∩→∩′ : ∀ {𝑨} {𝐴 : Set 𝑨} → {x y : 𝕃 𝐴} → ⌜ x ∩ y ≡∅⌝ → ⌜ x ∩′ y ≡∅⌝
-- -- -- --   ∩→∩′ {y = ∅} ε = ε
-- -- -- --   ∩→∩′ {y = ∷ y₀∉y₁s} ε = φ (∅⊂∷ y₀∉y₁s) ∉∅ {!!}
-- -- -- --   ∩→∩′ (φ ∅⊂x₀s x₀∉y₀s x₁) = {!!}

-- -- -- -- -- append : ∀ {𝑨} {𝐴 : Set 𝑨} → (x₀ : 𝐴) → (ys : 𝕃 𝐴) → (x₀∉ys : x₀ ∉ ys) → ∃ λ y₀sx₀ → ∀ {u} → u ∉ ys → u ≢ x₀ → u ∉ y₀sx₀
-- -- -- -- -- append x₀ ∅ _ = ∷ {x₀ = x₀} ∉∅ , (λ {u∉∅ u≢x₀ → ∉∷ u≢x₀ ∉∅ ∉∅})
-- -- -- -- -- append x₀ (∷ {y₀} {y₁s} y₀∉y₁s) (∉∷ x₀≢y₀ x₀∉y₁s .y₀∉y₁s) = ∷ {x₀ = y₀} {x₁s = fst (append x₀ y₁s x₀∉y₁s)} {!!} , {!!}

-- -- -- -- data ⌜_∩_≡∅⌝ {𝑨} {𝐴 : Set 𝑨} : 𝕃 𝐴 → 𝕃 𝐴 → Set 𝑨 where
-- -- -- --   ε : ∀ {y₀s} → ⌜ ∅ ∩ y₀s ≡∅⌝
-- -- -- --   φ : ∀ {x₀s y₀s} → (∅⊂x₀s : ∅⊂ x₀s) → (x₀∉y₀s : head ∅⊂x₀s ∉ y₀s) →  ⌜ tail ∅⊂x₀s ∩ ∷ x₀∉y₀s ≡∅⌝ → ⌜ x₀s ∩ y₀s ≡∅⌝
-- -- -- -- -- φ (abc ∩ def) → dabc ∩ ef
-- -- -- -- -- -- ∪ʳ abc def = cbadef
-- -- -- -- -- -- ∪ʳ a bcdef = abcdef
-- -- -- -- -- ∪ʳ : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀s y₀s} → ⌜ x₀s ∩ y₀s ≡∅⌝ → 𝕃 𝐴
-- -- -- -- -- ∪ʳ ∅ = ∅
-- -- -- -- -- ∪ʳ (ε (∅⊂∷ y₀s)) = {!y₀s!}
-- -- -- -- -- ∪ʳ (φ {x₀s} {y₀s} ∅⊂x₀s x₀∉y₀s x₁s∩x₀y₀s≡∅) = ∪ʳ x₁s∩x₀y₀s≡∅

-- -- -- -- -- -- ∪ʳ′ abc def = fedabc
-- -- -- -- -- -- ∪ʳ′ a bcdef = fedcba
-- -- -- -- -- ∪ʳ′ : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀s y₀s} → ⌜ x₀s ∩′ y₀s ≡∅⌝ → 𝕃 𝐴
-- -- -- -- -- ∪ʳ′ ∅ = ∅
-- -- -- -- -- ∪ʳ′ (ε {x₀s}) = x₀s
-- -- -- -- -- ∪ʳ′ (φ {x₀s} {y₀s} ∅⊂y₀s y₀∉x₀s y₀x₀s∩y₁s≡∅) = ∪ʳ′ y₀x₀s∩y₁s≡∅



-- -- -- -- -- {-
-- -- -- -- -- a ∩ (b ∩ (c ∩ (def)))
-- -- -- -- -- abc ∪ def = cbadef
-- -- -- -- -- x₀s
-- -- -- -- -- ∪ (x₀ ∩ x₁s               ≡∅)
-- -- -- -- -- ∪ (x₀ ∩ (∪ (x₁ ∩ x₂s ≡∅)) ≡∅)
-- -- -- -- -- ∪ (∪ (x₀ ∩ x₁ ≡∅) ∩ x₂s ≡∅)
-- -- -- -- -- -}

-- -- -- -- -- x∉yz→x∉y : ∀ {𝑨} {𝐴 : Set 𝑨} {x : 𝐴} {y z : 𝕃 𝐴} → (y∩z≡∅ : ⌜ y ∩ z ≡∅⌝) → x ∉ ∪ʳ y∩z≡∅ → x ∉ y
-- -- -- -- -- x∉yz→x∉y ∅ _ = ∉∅
-- -- -- -- -- x∉yz→x∉y (ε _) _ = ∉∅
-- -- -- -- -- x∉yz→x∉y (φ (∅⊂∷ y₀∉y₁s) y₀∉z y₁s∩y₀z≡∅) x∉y₁s∪y₀z = {!x∉y₁s∪y₀z!}

-- -- -- -- -- ∪∩-assoc : ∀ {𝑨} {𝐴 : Set 𝑨} {x yz y z : 𝕃 𝐴} → (y∩z≡∅ : ⌜ y ∩ z ≡∅⌝) → (x∩yz≡∅ : ⌜ x ∩ (∪ʳ y∩z≡∅) ≡∅⌝) → ⌜ x ∩ y ≡∅⌝
-- -- -- -- -- ∪∩-assoc {𝑨} {𝐴} {x} {yz} {y} {z} y∩z≡∅ x∩yz≡∅ = {!!}
-- -- -- -- -- --∪∩-assoc y∩z≡∅ ∅ = ?
-- -- -- -- -- --∪∩-assoc y∩z≡∅ (ε _) = ε
-- -- -- -- -- --∪∩-assoc y∩z≡∅ (φ ∅⊂x x₀∉yz x₁s∩x₀yz≡∅) = φ ∅⊂x {!!} {!!}

-- -- -- -- -- -- (y∩z≡∅ : ⌜ y ∩ z ≡∅⌝) → ∪
-- -- -- -- -- -- ⌜ xs ∩ (∪ ⌜ ys ∩ zs ≡∅⌝) ≡∅⌝ → ∪ (∪ ⌜ xs ∩ ys ≡∅⌝) (∪ ⌜ ys ∩ zs ≡∅⌝) ≡∅⌝

-- -- -- -- -- init[1] : ∀ {𝑨} {𝐴 : Set 𝑨} {L : 𝕃 𝐴} → ∅⊂ L → 𝕃 𝐴
-- -- -- -- -- init[1] (∅⊂∷ {x₀} ∉∅) = ∅
-- -- -- -- -- init[1] (∅⊂∷ {x₀} (∉∷ {x₁} x₀≢x₁ x₀∉∅                     ∉∅))                                             = ∷ x₀∉∅
-- -- -- -- -- init[1] (∅⊂∷ {x₀} (∉∷ {x₁} x₀≢x₁ x₀∉x₂s                   (∉∷ {x₂} x₁≢x₂ x₁∉∅   ∉∅)))                      = ∷ (∉∷ x₀≢x₁ ∉∅ ∉∅)
-- -- -- -- -- init[1] (∅⊂∷ {x₀} (∉∷ {x₁} x₀≢x₁ (∉∷ {x₂} x₀≢x₂ x₀∉x₃s _) (∉∷      x₁≢x₂ x₁∉x₃s (∉∷ {x₃} x₂≢x₃ x₂∉∅ ∉∅)))) = ∷ (∉∷ x₀≢x₁ (∉∷ x₀≢x₂ ∉∅ ∉∅) (∉∷ x₁≢x₂ ∉∅ ∉∅))
-- -- -- -- -- init[1] (∅⊂∷ (∉∷ x₀≢x₁ x₀∉x₁s (∉∷ x₁≢x₂ x₁∉x₂s (∉∷ x₃ x₂∉x₃s₂ (∉∷ x x₂∉x₃s₁ x₂∉x₃s))))) = {!!}
