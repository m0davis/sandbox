-- {-# OPTIONS --exact-split #-}

module Scratch where

module CcCr where
  data D : Set where
    d : D
   
  foo : D
  foo = {!!}

module UnquoteBug where
  open import Reflection using (TC ; Term)
  open import Data.Unit using (⊤)

  postulate
    error : ∀ {A : Set} → A

  macro
    buggy : Term → TC ⊤
    buggy = error

  test : Set
  test = {!buggy!}

module Category where
  open import Level
  open import Relation.Binary.Core
  open import Function
  record Functor {α} (F : Set α → Set α) : Set (suc α) where
    field
      map : ∀ {A B : Set α} → (A → B) → F A → F B

    field
      law-id : ∀ {X : Set α} {FX : F X} → map id FX ≡ FX
      law-composition : ∀ {A B C : Set α} {f : B → C} {g : A → B} {FA : F A} → (map f ∘ map g) FA ≡ map (f ∘ g) FA

module DataUniqueVector∉ where
  open import Level
  open import Relation.Binary.Core
  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Data.Nat renaming (suc to succ)
  open import Data.Maybe
  open import Data.Empty
  import Data.AVL renaming (Tree to Map)

  mutual
    data Vec {α} (A : Set α) : ℕ → Set α where
      []  : Vec A 0
      _∷_!_ : ∀ {n} (x : A) (xs : Vec A n) → (prf : x ∉ xs) → Vec A (succ n)
     
    data _∉_ {α} {A : Set α} (a : A) : {n : ℕ} → Vec A n → Set α where
      not-here  : ∀ {n} {x : A} {xs : Vec A n} → (x≢a : x ≢ a) → (a∉xs : a ∉ xs) (x∉xs : x ∉ xs) → a ∉ (x ∷ xs ! x∉xs)
      not-there : a ∉ []
 
  empty-prf : ∀ {α} {A : Set α} → (a : A) → a ∉ []
  empty-prf a = not-there
 
  sampleVec₁ : Vec ℕ 1
  sampleVec₁ = 1 ∷ [] ! not-there
 
  sampleVec₂ : Vec ℕ 2
  sampleVec₂ = 2 ∷ sampleVec₁ ! not-here (λ ()) not-there not-there
 
  sampleVec₃ : Vec ℕ 3
  sampleVec₃ = 2 ∷ sampleVec₂ ! not-here (λ x → {!!}) {!!} (not-here (λ ()) not-there not-there)

module DataUniqueList∉ where
  open import Level
  open import Relation.Binary.Core
  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Data.Nat renaming (suc to succ)
  open import Data.Maybe
  open import Data.Empty
  import Data.AVL renaming (Tree to Map)
 
  mutual
    data List {α} (A : Set α) : Set α where
      []  : List A
      _∷_!_ : ∀ (x : A) (xs : List A) → (prf : x ∉ xs) → List A
     
    data _∉_ {α} {A : Set α} (a : A) : List A → Set α where
      not-here  : ∀ {x : A} {xs : List A} → (x≢a : x ≢ a) → (a∉xs : a ∉ xs) (x∉xs : x ∉ xs) → a ∉ (x ∷ xs ! x∉xs)
      not-there : a ∉ []

module MaybeRecord where
  open import Level
  open import Relation.Binary.Core
  open import Data.Product
  open import Data.Sum
  open import Data.Unit.Base

  record Maybe {α} (A : Set α) : Set α where
    field
      unmaybe : ⊤ ⊎ A
 
  nothing : ∀ {α} {A : Set α} → Maybe A
  nothing = record { unmaybe = inj₁ tt }
 
  just : ∀ {α} {A : Set α} (a : A) → Maybe A
  just a = record { unmaybe = inj₂ a }

module RegularList where
  open import Level
  open import Relation.Binary.Core
  open import Data.Product
  open import Data.Sum
  open import Data.Unit.Base

  open MaybeRecord
  record Cons {α} (A : Set α) : Set α where
    inductive
    field
      uncons : Maybe (A × Cons A)
 
  ∅ : ∀ {α} {A : Set α} → Cons A
  ∅ = record { uncons = nothing }
 
  _∷_ : ∀ {α} {A : Set α} → A → Cons A → Cons A
  a ∷ as = record { uncons = just (a , as) }
 
  record _∈_ {α} {A : Set α} (a : A) (as : Cons A) : Set α where
    inductive
    field
      un∈ : (∃ λ as' → Cons.uncons as ≡ just (a , as')) ⊎ (∃ λ as' → ∃ λ a' → Cons.uncons as ≡ just (a' , as') → a ∈ as')

  record _∉_ {α} {A : Set α} (a : A) (as : Cons A) : Set α where
    inductive
    field
      un∉ : (∃ λ a' → ∃ λ as' → Cons.uncons as ≡ just (a' , as') → a ≢ a' × a ∉ as') ⊎ Cons.uncons as ≡ nothing

  module Map where
    record Map {α} {Key : Set α} (Value : Key → Set α) (keys : Cons Key) : Set α where
      inductive
      field
        unmap : Maybe (∃ λ (k : Key) → ∃ λ ks → Value k × Map Value ks)
    
module UniqueVec where
  open import Level
  open import Relation.Binary.Core
  open import Data.Product
  open import Data.Sum
  open import Data.Unit.Base

  open MaybeRecord
  open import Data.Nat renaming (suc to succ)
  mutual
    record Cons {α} (A : Set α) (n : ℕ) : Set α where
      inductive
      field
        uncons : Maybe (∃ λ (a : A) → ∃ λ (n' : ℕ) → n ≡ succ n' × ∃ λ (as : Cons A n') → a ∉ as)

    ∅ : ∀ {α} {n} {A : Set α} → Cons A n
    ∅ = record { uncons = nothing }      
   
    record _∉_ {α} {n} {A : Set α} (a : A) (as : Cons A n) : Set α where
      inductive
      field
        un∉ : (∃ λ a' → ∃ λ n' → (prf : n ≡ succ n') → ∃ λ (as' : Cons A n') → ∃ λ a'∉as' → Cons.uncons as ≡ just (a' , n' , prf , as' , a'∉as') → a ≢ a' × a ∉ as') ⊎ Cons.uncons as ≡ nothing

    _∷_!_ : ∀ {α} {n} {A : Set α} → (a : A) → (as : Cons A n) → a ∉ as → Cons A (succ n)
    _∷_!_ {n = n} a as a∉as = record { uncons = just (a , n , (refl , (as , a∉as))) }
   
module UniqueList where
  open import Level
  open import Relation.Binary.Core
  open import Data.Product
  open import Data.Sum
  open import Data.Unit.Base

  open MaybeRecord
  mutual
    record Cons {α} (A : Set α) : Set α where
      inductive
      field
        uncons : Maybe (∃ λ (a : A) → ∃ λ (as : Cons A) → a ∉ as)

    ∅ : ∀ {α} {A : Set α} → Cons A
    ∅ = record { uncons = nothing }      
   
    record _∉_ {α} {A : Set α} (a : A) (as : Cons A) : Set α where
      inductive
      field
        un∉ : (∃ λ a' → ∃ λ (as' : Cons A) → ∃ λ a'∉as' → Cons.uncons as ≡ just (a' , as' , a'∉as') × a ≢ a' × a ∉ as') ⊎ Cons.uncons as ≡ nothing

    _∷_!_ : ∀ {α} {A : Set α} → (a : A) → (as : Cons A) → a ∉ as → Cons A
    _∷_!_ a as a∉as = record { uncons = just (a , ((as , a∉as))) }

  open import Data.Nat renaming (suc to succ)

  sampleUL₁ : Cons ℕ
  sampleUL₁ = 1 ∷ ∅ ! record { un∉ = inj₂ refl }

  sampleUL₂ : Cons ℕ
  sampleUL₂ = 2 ∷ sampleUL₁ ! record { un∉ = inj₁ (1 , (∅ , ((record { un∉ = inj₂ refl }) , refl , ((λ ()) , (record { un∉ = inj₂ refl }))))) }

  sampleUL₂' : Cons ℕ
  sampleUL₂' = 1 ∷ sampleUL₁ ! record { un∉ = inj₁ (1 , (∅ , ((record { un∉ = inj₂ refl }) , refl , ({!!} , (record { un∉ = inj₂ refl }))))) }

module FreeRecord where
  open import Level
  open import Relation.Binary.Core
  open import Data.Product
  open import Data.Sum
  open import Data.Unit.Base

  record Free {α} (F : Set α → Set α) (A : Set α) : Set (suc α) where
    inductive
    field
      unfree : A ⊎ (∃ λ x → (x → Free F A) × F x)

module VerticalBarProblemSolved where
  open import Data.Bool.Base using (Bool ; true ; false)
  open import Data.Product using (∃ ; _,_)
  open import Relation.Nullary using (yes ; no)
  open import Relation.Binary using (IsDecEquivalence)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Data.Empty using (⊥-elim)
  open import Function using (case_of_)
 
  module _ {isDecEquivalence : IsDecEquivalence {A = ℕ} _≡_} where
    open IsDecEquivalence isDecEquivalence using (_≟_)

    sucIffTrue : ℕ → Bool → ℕ
    sucIffTrue n true = suc n
    sucIffTrue n false with n ≟ n
    sucIffTrue n false | yes refl = n
    sucIffTrue n false | no n≢n = n

    lemma-easy : (n : ℕ) → sucIffTrue n false ≡ n
    lemma-easy n with n ≟ n
    lemma-easy n | yes refl = refl
    lemma-easy n | no n≢n = refl

    lemma-hard : (n : ℕ) → ∃ λ (b : Bool) → sucIffTrue n b ≡ n
    lemma-hard n = false , lemma-easy n

    lemma-easy' : {n : ℕ} → n ≡ n → sucIffTrue n false ≡ n
    lemma-easy' refl = {!!}

    lemma-hard' : (n : ℕ) → ∃ λ (b : Bool) → sucIffTrue n b ≡ n
    lemma-hard' n = false , (case (n ≟ n) of (λ { (yes refl) → {!!} ; (no n≢n) → ⊥-elim (n≢n refl) }))

module RewriteOnRight where
  open import Data.Product using (∃ ; _,_)
  open import Relation.Nullary using (Dec ; yes ; no)
  open import Function using (case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; cong ; refl)

  postulate
    K : Set
    V : K → Set
    M : Set
    _∈_ : K → M → Set
    get : ∀ {k : K} {m : M} → k ∈ m → V k
    isDecEquivalence/K : IsDecEquivalence {A = K} _≡_

  open IsDecEquivalence isDecEquivalence/K using (_≟_ ; sym)

  foo-helper :
    ∀ {x : M}
      {y : M}
      {a : K}
      {b : K}
      {a∈x : a ∈ x}
      {b∈x : b ∈ x}
      {a∈y : a ∈ y}
      (gax≡gay : get a∈x ≡ get a∈y)
      (a≡b : a ≡ b)
      (gbx≡gax : get b∈x ≡ subst V a≡b (get a∈x))
      → get b∈x ≡ get (subst (λ k → k ∈ y) a≡b a∈y)
  foo-helper gax≡gay a≡b gbx≡gax rewrite a≡b = trans gbx≡gax gax≡gay

  foo : ∀ {x : M}
          {y : M}
          (a : K)
          (b : K)
          {a∈x : a ∈ x}
          {b∈x : b ∈ x}
          {a∈y : a ∈ y}
          (gax≡gay : get a∈x ≡ get a∈y)
        → Dec (∃ λ (a≡b : a ≡ b) → (gbx≡gax : get b∈x ≡ subst V a≡b (get a∈x)) → get b∈x ≡ get (subst (λ k → k ∈ y) a≡b a∈y))
  foo a b gax≡gay = case a ≟ b of λ
    { (yes a≡b) → yes (a≡b , (λ {gbx≡gax → foo-helper gax≡gay a≡b gbx≡gax}))
    ; (no a≢b) → no (λ { (a≡b , _) → contradiction a≡b a≢b })
    }

  bar : ∀ {x : M}
          {y : M}
          (a : K)
          (b : K)
          {a∈x : a ∈ x}
          (b∈x : b ∈ x)
          {a∈y : a ∈ y}
          (gax≡gay : get a∈x ≡ get a∈y)
        → Dec (∃ λ (a≡b : a ≡ b) → (gbx≡gax : get b∈x ≡ subst V a≡b (get a∈x)) → get b∈x ≡ get (subst (λ k → k ∈ y) a≡b a∈y))
  bar a  b _   _       with a ≟ b
  bar _ ._ b∈x gax≡gay | yes refl = yes (refl , (λ {gbx≡gax → trans gbx≡gax gax≡gay}))
  bar _  _ _   _       | no a≢b = no (λ { (a≡b , _) → contradiction a≡b a≢b })

  get-commutes-with-subst :
    ∀ {a b : K}
      {a≡b : a ≡ b}
      {y : M}
      {a∈y : a ∈ y}
    → subst V a≡b (get a∈y) ≡ get (subst (λ k → k ∈ y) a≡b a∈y)
  get-commutes-with-subst {a≡b = refl} = refl

  baz : ∀ {x : M}
          {y : M}
          (a : K)
          (b : K)
          {a∈x : a ∈ x}
          {b∈x : b ∈ x}
          {a∈y : a ∈ y}
          (gax≡gay : get a∈x ≡ get a∈y)
        → Dec (∃ λ (a≡b : a ≡ b) → (gbx≡gax : get b∈x ≡ subst V a≡b (get a∈x)) → get b∈x ≡ get (subst (λ k → k ∈ y) a≡b a∈y))
  baz a b gax≡gay = case a ≟ b of λ
    { (yes a≡b) → yes (a≡b , (λ {gbx≡gax → trans gbx≡gax (trans (cong (subst V a≡b) gax≡gay) (get-commutes-with-subst {a≡b = a≡b}))}))
    ; (no a≢b) → no (λ { (a≡b , _) → contradiction a≡b a≢b })
    }

module OscarDebug where
  postulate
    A : Set

  data _⋒_ : (X : Set) → (Y : Set) → Set₁ where
    PureFree : (X : Set) → (Y : Set) → X ⋒ Y
      
  data _⋐_ : (X : Set) {Y : Set} (X⋒Y : X ⋒ Y) → Set₁ where
    PureFree : (X : Set) → (Y : Set) → X ⋐ PureFree X Y

  data _∈_ : (a : A) → {X : Set} {Y : Set} {X⋒Y : X ⋒ Y} (X⋐X⋒Y : X ⋐ X⋒Y) → Set₁ where
    singleton : (a : A) → (X : Set) (Y : Set) → a ∈ PureFree X Y

  foo : ∀
    {X Y : Set}
    {X⋒Y : X ⋒ Y}
    (X⋐X⋒Y : X ⋐ X⋒Y)
    → ∀ {a}
    → a ∈ X⋐X⋒Y
    → Set
  foo (PureFree x y) {a = a} = (λ { (singleton .a .x .y) → A })

module OscarDebug' where
  postulate
    A : Set

  data _⋒_ : (X : Set) → (Y : Set) → Set₁ where
    PureFree : (X : Set) → (Y : Set) → X ⋒ Y
      
  data _∈_ : (a : A) → {X : Set} {Y : Set} (X⋒Y : X ⋒ Y) → Set₁ where
    singleton : (a : A) → (X : Set) (Y : Set) → a ∈ PureFree X Y

  foo : ∀
    {X Y : Set}
    (X⋒Y : X ⋒ Y)
    → ∀ {a}
    → a ∈ X⋒Y
    → Set
  foo (PureFree x y) {a = a} = (λ { (singleton .a .x .y) → {!!} })
      where
    helper : ∀
      {X : Set}
      {Y : Set}
      → ∀ {a} (a∈X⋐X⋒Y : a ∈ PureFree X Y) → Set
    helper (singleton a x y) = A

module OscarDebug'' where
  data D : (X : Set) → Set₁ where
    d : (X : Set) → D X
      
  data _∈_ : (A : Set) {X : Set} (d : D X) → Set₁ where
    e : (A : Set) → (X : Set) → A ∈ d X

  foo : ∀ {X : Set} (d : D X) → ∀ {a} → a ∈ d → Set
  foo (d x) = λ {a∈d → {!a∈d!} } where
         
    helper : ∀ {X : Set} → ∀ {a} (a∈d : a ∈ d X) → Set
    helper (e a x) = {!!}

module OscarDebug''' where
  data D : Set where
    d : D
      
  data _∈_ : (A : Set) (d : D) → Set where
    e : (A : Set) → A ∈ d

  foo : (d : D) → ∀ {a} → a ∈ d → Set
  foo d = λ {a∈d → {!a∈d!} } where
         
    helper : ∀ {a} (a∈d : a ∈ d) → Set
    helper (e a) = {!!}

module OscarDebug4 where
  data D : Set where
    d : D
      
  data _∈_ : (A : Set) (d : D) → Set where
    e : (A : Set) → A ∈ d

  foo : (A : Set) (d : D) → A ∈ d → Set
  foo A d = λ { (e .A) → {!!} } where
         
    helper : (A : Set) → A ∈ d → Set
    helper A (e .A) = {!!}

module OscarDebug5 where
  open import Data.Product
  open import Relation.Nullary.Decidable

  postulate
    A : Set

  data D : (a : A) → Set where
    d : (a : A) → D a
      
  data _∈_ : (a : A) (da : D a) → Set where
    e : (a : A) → a ∈ d a

  foo : (a a' : A) (da : D a) → ∃ λ da' → a' ∈ da'
  foo a a' = λ da' → d a' , e a'

module ReflTries where
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Sum
  open import Data.Product
  open import Function
  open import Data.Empty

  postulate
    A : Set
    
  postulate
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_

  open IsDecEquivalence isDecEquivalence/A using (_≟_)

  data Foo : A → A → Set where
    foo : (a : A) → Foo a a

  bar : (a b : A) → Dec (Foo a b)
  bar a b with a ≟ b
  bar a .a | yes _≡_.refl = yes (foo a)
  ... | no an=b = {!!}

  baz : (a b : A) (a≢b : a ≢ b) → Foo a b → ⊥
  baz b .b a≢b (foo .b) = a≢b refl

  baz' : (a b : A) (a≢b : a ≢ b) → Dec (Foo a b)
  baz' a b a≢b = no (λ {fab → {!!}})

  bar' : (a b : A) → Dec (Foo a b)
  bar' a b with a ≟ b
  bar' a b | yes a≡b = yes (subst _ a≡b (foo a))
  bar' a b | no a≢b = no (baz a b a≢b)

  bar'' : (a b : A) → Dec (Foo a b)
  bar'' a b with a ≟ b
  bar'' a b | yes a≡b = yes (subst (Foo a) a≡b (foo a))
  bar'' a b | no a≢b = no (λ x → contradiction {!!} {!!})


  qux : (a b : A) → Dec (Foo a b)
  qux a b = case a ≟ b of λ
    { (yes a≡b) → yes (subst _ a≡b (foo a))
    ; (no a≢b) → no (baz a b a≢b) }

  qux' : (a b : A) → Dec (Foo a b)
  qux' a b = case a ≟ b of λ
    { (yes a≡b) → subst (λ v → Dec (Foo a v)) a≡b (yes {!!})
    ; (no a≢b) → no (baz a b a≢b) }

module OscarMetaProblem'₅ where
  open import Data.List.Base
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Sum
  open import Data.Product
  open import Function
  open import Data.Nat.Base hiding (_≟_; suc)
  open import Data.Empty

  postulate
    A : Set
    
  V : A → Set
  V = λ _ → A

  postulate
    M : ℕ → Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_
    isDecEquivalence/V : (a : A) → IsDecEquivalence {A = V a} _≡_

--  open import Map


  open import Level using () renaming (suc to sucₗ ; _⊔_ to _⊔ₗ_ )
  open import Relation.Binary.Core using (_≡_ ; _≢_)
  open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Function using (_$_ ; case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence ; Rel)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl ; module ≡-Reasoning)
  open import Relation.Binary.HeterogeneousEquality as H using (_≅_)

  record Map 
           {K : Set}
           (V : K → Set)
           (Carrier : ℕ → Set) (isDecEquivalence/K : IsDecEquivalence {A = K} _≡_) (isDecEquivalence/V : (k : K) → IsDecEquivalence {A = V k} _≡_) : Set₁ where
    open IsDecEquivalence isDecEquivalence/K using (_≟_ ; sym)
    field
      ∅ : Carrier 0
      _∉_ : ∀ {s} → K → Carrier s → Set
      ∅-is-empty : ∀ {𝑘} {∅ : Carrier 0} → 𝑘 ∉ ∅
      
    _∈_ : ∀ {s} → K → Carrier s → Set
    _∈_ k m = ¬ k ∉ m
 
    field
      get : ∀ {k : K} {s} {m : Carrier s} → k ∈ m → V k
      get-is-unique : ∀ {k : K} {s} {m : Carrier s} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get k∈m¹ ≡ get k∈m²
      
    infixl 40 _⊆_
    _⊆_ : ∀ {s₁ s₀} → Carrier s₁ → Carrier s₀ → Set
    _⊆_ m₁ m₀ = ∀ {𝑘} → (𝑘∈m₁ : 𝑘 ∈ m₁) → ∃ λ (𝑘∈m₀ : 𝑘 ∈ m₀) → get 𝑘∈m₁ ≡ get 𝑘∈m₀
 
    infixl 40 _⊂_∣_
    _⊂_∣_ : ∀ {s₀ s₁} → Carrier s₀ → Carrier s₁ → (K → Set) → Set
    _⊂_∣_ m₀ m₁ c = ∀ {𝑘} → c 𝑘 → (𝑘∈m₀ : 𝑘 ∈ m₀) → ∃ λ (𝑘∈m₁ : 𝑘 ∈ m₁) → get 𝑘∈m₀ ≡ get 𝑘∈m₁
 
    field
      put : ∀ {k₀ : K} (v₀ : V k₀) {s₁} {m₁ : Carrier s₁} → k₀ ∉ m₁ → ∃ λ (m₀ : Carrier (suc s₁)) → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get k₀∈m₀ ≡ v₀ × m₁ ⊆ m₀ × m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀
      pick : ∀ {k₀ : K} {s₁} {m₀ : Carrier (suc s₁)} → k₀ ∈ m₀ → ∃ λ (m₁ : Carrier s₁) → m₁ ⊆ m₀ × (m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀) × k₀ ∉ m₁

  postulate
    m : Map V M isDecEquivalence/A isDecEquivalence/V  

  data _⋐_ : (X : A) (ns : A) → Set where
    PureFree : (x : A) → (ns : A) → x ⋐ ns

  data _∈pf_ : (a : A) → {X : A} {ns : A} (X⋐X⋒Y : X ⋐ ns) → Set where
    singleton : (a : A) → (ns : A)→ a ∈pf PureFree a ns
    
  getpf : ∀ {a : A} {X : A} {ns : A}  {X⋐X⋒Y : X ⋐ ns} → (a ∈pf X⋐X⋒Y) → A
  getpf (singleton a ns) = ns

--  open Map.Map m
  open Map m

  reduce-PureFree-to-map' : ∀
    {PAT : A}
    {ns : A}
    (PAT⋐PAT⋒EXP : PAT ⋐ ns)
    → Dec $ ∃ λ s → ∃ λ (binding : M s) → ∀ {a} (a∈binding : a ∈ binding) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PAT⋐PAT⋒EXP) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
  reduce-PureFree-to-map' (PureFree x ns) =
    yes $
      1 ,
      (proj₁ $ put {k₀ = x} ns {m₁ = ∅} ∅-is-empty) ,
       (λ {a∈binding → helper2 a∈binding})
 {-      
      (λ { {a} a∈binding → case IsDecEquivalence._≟_ isDecEquivalence/A x a of
        (λ
        { (yes p) → subst _ (sym p) (singleton a ns) ,
                    (let s1 , s2 , s3 , s4
                                        = put {k₀ = a} ns {m₁ = ∅} ∅-is-empty
                      in trans (get-is-unique a∈binding (subst _ (sym p) s2)) (subst _ (sym p) s3)
                    )
        ; (no ¬p) → {!!} })
        })
 -}        
{-
/home/martin/Desktop/Sandbox.agda:1121,141-159
Cannot instantiate the metavariable _3268 to solution get (subst (λ
v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥) (sym p)
(proj₁ (proj₂ (put (free g ns) ∅-is-empty)))) ≡ _k_3215 x g ns
a∈binding p since it contains the variable p which is not in scope
of the metavariable or irrelevant in the metavariable but relevant
in the solution
when checking that the expression subst _ (sym p) s3 has type
get
(subst
 (λ v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥)
 (sym p) (proj₁ (proj₂ (put (free g ns) ∅-is-empty))))
≡ _k_3215 x g ns a∈binding p
-}

-- trans (get-is-unique a∈binding (subst _ (sym p) s2)) (subst _ (sym p) s3))
      where
    helper2 : ∀
      {x : A}
      {ns : A}
      → ∀ {a} (a∈binding : a ∈ proj₁ (put {k₀ = x} ns {m₁ = ∅} ∅-is-empty)) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PureFree x ns) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
    helper2 {x₁} {ns₁} {a} a∈binding with (IsDecEquivalence._≟_ isDecEquivalence/A)  x₁ a
    helper2 {a}  {ns₁} {.a} a∈binding | yes refl = (singleton a ns₁) , (let (s1 , s2 , s3 , s4) = (put  {k₀ = a} ns₁ {m₁ = ∅} ∅-is-empty) in trans (get-is-unique a∈binding s2) s3)    
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ with pick a∈binding
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ | m0 , k∈m0→Σ , k≢a→k∈m1→Σ , a∉m0 = let s1 , s2 , s3 , s4
                                                                                                     = put {k₀ = x₁} ns₁ {m₁ = ∅} ∅-is-empty
                                                                                               in contradiction ∅-is-empty (proj₁ (k≢a→k∈m1→Σ a≢x₁ s2))

module OscarMetaProblem'₆ where
  open import Data.List.Base
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Sum
  open import Data.Product
  open import Function
  open import Data.Nat.Base hiding (_≟_; suc)
  open import Data.Empty
  open import Relation.Binary.Core using (_≡_ ; _≢_)
  open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Function using (_$_ ; case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence ; Rel)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl)

  postulate
    A : Set
    
  V : A → Set
  V = λ _ → A

  postulate
    M : ℕ → Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_
    isDecEquivalence/V : (a : A) → IsDecEquivalence {A = V a} _≡_

  record Map 
           {K : Set}
           (V : K → Set)
           (Carrier : ℕ → Set) (isDecEquivalence/K : IsDecEquivalence {A = K} _≡_) (isDecEquivalence/V : (k : K) → IsDecEquivalence {A = V k} _≡_) : Set₁ where
    open IsDecEquivalence isDecEquivalence/K using (_≟_ ; sym)
    field
      ∅ : Carrier 0
      _∉_ : ∀ {s} → K → Carrier s → Set
      ∅-is-empty : ∀ {𝑘} {∅ : Carrier 0} → 𝑘 ∉ ∅
      
    _∈_ : ∀ {s} → K → Carrier s → Set
    _∈_ k m = ¬ k ∉ m
 
    field
      get : ∀ {k : K} {s} {m : Carrier s} → k ∈ m → V k
      get-is-unique : ∀ {k : K} {s} {m : Carrier s} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get k∈m¹ ≡ get k∈m²
      
    infixl 40 _⊆_
    _⊆_ : ∀ {s₁ s₀} → Carrier s₁ → Carrier s₀ → Set
    _⊆_ m₁ m₀ = ∀ {𝑘} → (𝑘∈m₁ : 𝑘 ∈ m₁) → ∃ λ (𝑘∈m₀ : 𝑘 ∈ m₀) → get 𝑘∈m₁ ≡ get 𝑘∈m₀
 
    infixl 40 _⊂_∣_
    _⊂_∣_ : ∀ {s₀ s₁} → Carrier s₀ → Carrier s₁ → (K → Set) → Set
    _⊂_∣_ m₀ m₁ c = ∀ {𝑘} → c 𝑘 → (𝑘∈m₀ : 𝑘 ∈ m₀) → ∃ λ (𝑘∈m₁ : 𝑘 ∈ m₁) → get 𝑘∈m₀ ≡ get 𝑘∈m₁
 
    field
      put : ∀ {k₀ : K} (v₀ : V k₀) {s₁} {m₁ : Carrier s₁} → k₀ ∉ m₁ → ∃ λ (m₀ : Carrier (suc s₁)) → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get k₀∈m₀ ≡ v₀ × m₁ ⊆ m₀ × m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀
      pick : ∀ {k₀ : K} {s₁} {m₀ : Carrier (suc s₁)} → k₀ ∈ m₀ → ∃ λ (m₁ : Carrier s₁) → m₁ ⊆ m₀ × (m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀) × k₀ ∉ m₁

  postulate
    m : Map V M isDecEquivalence/A isDecEquivalence/V  

  data _⋐_ : (X : A) (ns : A) → Set where
    PureFree : (x : A) → (ns : A) → x ⋐ ns

  data _∈pf_ : (a : A) → {X : A} {ns : A} (X⋐X⋒Y : X ⋐ ns) → Set where
    singleton : (a : A) → (ns : A)→ a ∈pf PureFree a ns
    
  getpf : ∀ {a : A} {X : A} {ns : A}  {X⋐X⋒Y : X ⋐ ns} → (a ∈pf X⋐X⋒Y) → A
  getpf (singleton a ns) = ns

  open Map m

  reduce-PureFree-to-map' : ∀
    {PAT : A}
    {ns : A}
    (PAT⋐PAT⋒EXP : PAT ⋐ ns)
    → Dec $ ∃ λ (binding : M 1) → ∀ {a} (a∈binding : a ∈ binding) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PAT⋐PAT⋒EXP) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
  reduce-PureFree-to-map' (PureFree x ns) =
    yes $
      (proj₁ $ put {k₀ = x} ns {m₁ = ∅} ∅-is-empty) ,
       (λ {a∈binding → helper2 a∈binding})
 {-      
      (λ { {a} a∈binding → case IsDecEquivalence._≟_ isDecEquivalence/A x a of
        (λ
        { (yes p) → subst _ (sym p) (singleton a ns) ,
                    (let s1 , s2 , s3 , s4
                                        = put {k₀ = a} ns {m₁ = ∅} ∅-is-empty
                      in trans (get-is-unique a∈binding (subst _ (sym p) s2)) (subst _ (sym p) s3)
                    )
        ; (no ¬p) → {!!} })
        })
 -}        
{-
/home/martin/Desktop/Sandbox.agda:1121,141-159
Cannot instantiate the metavariable _3268 to solution get (subst (λ
v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥) (sym p)
(proj₁ (proj₂ (put (free g ns) ∅-is-empty)))) ≡ _k_3215 x g ns
a∈binding p since it contains the variable p which is not in scope
of the metavariable or irrelevant in the metavariable but relevant
in the solution
when checking that the expression subst _ (sym p) s3 has type
get
(subst
 (λ v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥)
 (sym p) (proj₁ (proj₂ (put (free g ns) ∅-is-empty))))
≡ _k_3215 x g ns a∈binding p
-}
      where
    helper2 : ∀
      {x : A}
      {ns : A}
      → ∀ {a} (a∈binding : a ∈ proj₁ (put {k₀ = x} ns {m₁ = ∅} ∅-is-empty)) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PureFree x ns) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
    helper2 {x₁} {ns₁} {a} a∈binding with (IsDecEquivalence._≟_ isDecEquivalence/A)  x₁ a
    helper2 {a}  {ns₁} {.a} a∈binding | yes refl = (singleton a ns₁) , (let (s1 , s2 , s3 , s4) = (put  {k₀ = a} ns₁ {m₁ = ∅} ∅-is-empty) in trans (get-is-unique a∈binding s2) s3)    
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ with pick a∈binding
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ | m0 , k∈m0→Σ , k≢a→k∈m1→Σ , a∉m0 = let s1 , s2 , s3 , s4
                                                                                                     = put {k₀ = x₁} ns₁ {m₁ = ∅} ∅-is-empty
                                                                                               in contradiction ∅-is-empty (proj₁ (k≢a→k∈m1→Σ a≢x₁ s2))

module OscarMetaProblem'₇ where
  open import Data.List.Base
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Sum
  open import Data.Product
  open import Function
  open import Data.Nat.Base hiding (_≟_; suc)
  open import Data.Empty
  open import Relation.Binary.Core using (_≡_ ; _≢_)
  open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Function using (_$_ ; case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence ; Rel)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl)

  postulate
    A : Set
    
  V : A → Set
  V = λ _ → A

  postulate
    M : ℕ → Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_
    isDecEquivalence/V : (a : A) → IsDecEquivalence {A = V a} _≡_

  record Map 
           {K : Set}
           (V : K → Set)
           (Carrier : ℕ → Set) : Set₁ where
    field
      ∅ : Carrier 0
      _∉_ : ∀ {s} → K → Carrier s → Set
      ∅-is-empty : ∀ {𝑘} {∅ : Carrier 0} → 𝑘 ∉ ∅
      
    _∈_ : ∀ {s} → K → Carrier s → Set
    _∈_ k m = ¬ k ∉ m
 
    field
      get : ∀ {k : K} {s} {m : Carrier s} → k ∈ m → V k
      get-is-unique : ∀ {k : K} {s} {m : Carrier s} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get k∈m¹ ≡ get k∈m²
      
    infixl 40 _⊂_∣_
    _⊂_∣_ : ∀ {s₀ s₁} → Carrier s₀ → Carrier s₁ → (K → Set) → Set
    _⊂_∣_ m₀ m₁ c = ∀ {𝑘} → c 𝑘 → (𝑘∈m₀ : 𝑘 ∈ m₀) → ∃ λ (𝑘∈m₁ : 𝑘 ∈ m₁) → get 𝑘∈m₀ ≡ get 𝑘∈m₁
 
    field
      put : ∀ {k₀ : K} (v₀ : V k₀) {s₁} {m₁ : Carrier s₁} → k₀ ∉ m₁ → ∃ λ (m₀ : Carrier (suc s₁)) → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get k₀∈m₀ ≡ v₀
      pick : ∀ {k₀ : K} {s₁} {m₀ : Carrier (suc s₁)} → k₀ ∈ m₀ → ∃ λ (m₁ : Carrier s₁) → (m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀)

  postulate
    m : Map V M

  data _⋐_ : (X : A) (ns : A) → Set where
    PureFree : (x : A) → (ns : A) → x ⋐ ns

  data _∈pf_ : (a : A) → {X : A} {ns : A} (X⋐X⋒Y : X ⋐ ns) → Set where
    singleton : (a : A) → (ns : A)→ a ∈pf PureFree a ns
    
  getpf : ∀ {a : A} {X : A} {ns : A}  {X⋐X⋒Y : X ⋐ ns} → (a ∈pf X⋐X⋒Y) → A
  getpf (singleton a ns) = ns

  open Map m

  reduce-PureFree-to-map' : ∀
    {PAT : A}
    {ns : A}
    (PAT⋐PAT⋒EXP : PAT ⋐ ns)
    → Dec $ ∃ λ (binding : M 1) → ∀ {a} (a∈binding : a ∈ binding) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PAT⋐PAT⋒EXP) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
  reduce-PureFree-to-map' (PureFree x ns) =
    yes $
      (proj₁ $ put {k₀ = x} ns {m₁ = ∅} ∅-is-empty) ,
       (λ {a∈binding → helper2 a∈binding})
 {-      
      (λ { {a} a∈binding → case IsDecEquivalence._≟_ isDecEquivalence/A x a of
        (λ
        { (yes p) → subst _ (sym p) (singleton a ns) ,
                    (let s1 , s2 , s3
                                        = put {k₀ = a} ns {m₁ = ∅} ∅-is-empty
                      in trans (get-is-unique a∈binding (subst _ (sym p) s2)) (subst _ (sym p) s3)
                    )
        ; (no ¬p) → {!!} })
        })
 -}        
{-
/home/martin/Desktop/Sandbox.agda:1121,141-159
Cannot instantiate the metavariable _3268 to solution get (subst (λ
v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥) (sym p)
(proj₁ (proj₂ (put (free g ns) ∅-is-empty)))) ≡ _k_3215 x g ns
a∈binding p since it contains the variable p which is not in scope
of the metavariable or irrelevant in the metavariable but relevant
in the solution
when checking that the expression subst _ (sym p) s3 has type
get
(subst
 (λ v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥)
 (sym p) (proj₁ (proj₂ (put (free g ns) ∅-is-empty))))
≡ _k_3215 x g ns a∈binding p
-}
      where
    helper2 : ∀
      {x : A}
      {ns : A}
      → ∀ {a} (a∈binding : a ∈ proj₁ (put {k₀ = x} ns {m₁ = ∅} ∅-is-empty)) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PureFree x ns) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
    helper2 {x₁} {ns₁} {a} a∈binding with (IsDecEquivalence._≟_ isDecEquivalence/A)  x₁ a
    helper2 {a}  {ns₁} {.a} a∈binding | yes refl = (singleton a ns₁) , (let (s1 , s2 , s3) = (put  {k₀ = a} ns₁ {m₁ = ∅} ∅-is-empty) in trans (get-is-unique a∈binding s2) s3)    
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ with pick a∈binding
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ | _ , k≢a→k∈m1→Σ = let s1 , s2 , s3 = put {k₀ = x₁} ns₁ {m₁ = ∅} ∅-is-empty in contradiction ∅-is-empty (proj₁ (k≢a→k∈m1→Σ a≢x₁ s2))

module OscarMetaProblem'₈ where
  open import Data.List.Base
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Sum
  open import Data.Product
  open import Function
  open import Data.Nat.Base hiding (_≟_; suc)
  open import Data.Empty
  open import Relation.Binary.Core using (_≡_ ; _≢_)
  open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Function using (_$_ ; case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence ; Rel)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl)

  postulate
    A : Set
    
  V : A → Set
  V = λ _ → A

  postulate
    M : Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_
    isDecEquivalence/V : (a : A) → IsDecEquivalence {A = V a} _≡_

  postulate
    ∅ : M
    _∉_ : A → M → Set
    ∅-is-empty : ∀ {𝑘} {∅ : M} → 𝑘 ∉ ∅
    
  _∈_ : A → M → Set
  _∈_ k m = ¬ k ∉ m

  postulate
    get : ∀ {k : A} {m : M} → k ∈ m → V k
    get-is-unique : ∀ {k : A} {m : M} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get k∈m¹ ≡ get k∈m²
    
  infixl 40 _⊂_∣_
  _⊂_∣_ : M → M → (A → Set) → Set
  _⊂_∣_ m₀ m₁ c = ∀ {𝑘} → c 𝑘 → (𝑘∈m₀ : 𝑘 ∈ m₀) → ∃ λ (𝑘∈m₁ : 𝑘 ∈ m₁) → get 𝑘∈m₀ ≡ get 𝑘∈m₁

  postulate
    put : ∀ {k₀ : A} (v₀ : V k₀) {m₁ : M} → k₀ ∉ m₁ → ∃ λ (m₀ : M) → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get k₀∈m₀ ≡ v₀
    pick : ∀ {k₀ : A} {m₀ : M} → k₀ ∈ m₀ → ∃ λ (m₁ : M) → (m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀)

  data _⋐_ : (X : A) (ns : A) → Set where
    PureFree : (x : A) → (ns : A) → x ⋐ ns

  data _∈pf_ : (a : A) → {X : A} {ns : A} (X⋐X⋒Y : X ⋐ ns) → Set where
    singleton : (a : A) → (ns : A)→ a ∈pf PureFree a ns
    
  getpf : ∀ {a : A} {X : A} {ns : A}  {X⋐X⋒Y : X ⋐ ns} → (a ∈pf X⋐X⋒Y) → A
  getpf (singleton a ns) = ns

  reduce-PureFree-to-map' : ∀
    {PAT : A}
    {ns : A}
    (PAT⋐PAT⋒EXP : PAT ⋐ ns)
    → Dec $ ∃ λ (binding : M) → ∀ {a} (a∈binding : a ∈ binding) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PAT⋐PAT⋒EXP) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
  reduce-PureFree-to-map' (PureFree x ns) =
    yes $
      (proj₁ $ put {k₀ = x} ns {m₁ = ∅} ∅-is-empty) ,
       (λ {a∈binding → helper2 a∈binding})
 {-      
      (λ { {a} a∈binding → case IsDecEquivalence._≟_ isDecEquivalence/A x a of
        (λ
        { (yes p) → subst _ (sym p) (singleton a ns) ,
                    (let s1 , s2 , s3
                                        = put {k₀ = a} ns {m₁ = ∅} ∅-is-empty
                      in trans (get-is-unique a∈binding (subst _ (sym p) s2)) (subst _ (sym p) s3)
                    )
        ; (no ¬p) → {!!} })
        })
 -}        
{-
/home/martin/Desktop/Sandbox.agda:1121,141-159
Cannot instantiate the metavariable _3268 to solution get (subst (λ
v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥) (sym p)
(proj₁ (proj₂ (put (free g ns) ∅-is-empty)))) ≡ _k_3215 x g ns
a∈binding p since it contains the variable p which is not in scope
of the metavariable or irrelevant in the metavariable but relevant
in the solution
when checking that the expression subst _ (sym p) s3 has type
get
(subst
 (λ v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥)
 (sym p) (proj₁ (proj₂ (put (free g ns) ∅-is-empty))))
≡ _k_3215 x g ns a∈binding p
-}
      where
    helper2 : ∀
      {x : A}
      {ns : A}
      → ∀ {a} (a∈binding : a ∈ proj₁ (put {k₀ = x} ns {m₁ = ∅} ∅-is-empty)) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PureFree x ns) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
    helper2 {x₁} {ns₁} {a} a∈binding with (IsDecEquivalence._≟_ isDecEquivalence/A)  x₁ a
    helper2 {a}  {ns₁} {.a} a∈binding | yes refl = (singleton a ns₁) , (let (s1 , s2 , s3) = (put  {k₀ = a} ns₁ {m₁ = ∅} ∅-is-empty) in trans (get-is-unique a∈binding s2) s3)    
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ with pick a∈binding
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ | _ , k≢a→k∈m1→Σ = let s1 , s2 , s3 = put {k₀ = x₁} ns₁ {m₁ = ∅} ∅-is-empty in contradiction ∅-is-empty (proj₁ (k≢a→k∈m1→Σ a≢x₁ s2))

module OscarMetaProblem'₉ where
  open import Data.List.Base
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Sum
  open import Data.Product
  open import Function
  open import Data.Nat.Base hiding (_≟_; suc)
  open import Data.Empty
  open import Relation.Binary.Core using (_≡_ ; _≢_)
  open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Function using (_$_ ; case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence ; Rel)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl)

  postulate
    A : Set
    
  V : Set
  V = A

  postulate
    M : Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_
    isDecEquivalence/V : (a : A) → IsDecEquivalence {A = V} _≡_

  postulate
    ∅ : M
    _∉_ : A → M → Set
    ∅-is-empty : ∀ {𝑘} {∅ : M} → 𝑘 ∉ ∅
    
  _∈_ : A → M → Set
  _∈_ k m = ¬ k ∉ m

  postulate
    get : ∀ {k : A} {m : M} → k ∈ m → V
    get-is-unique : ∀ {k : A} {m : M} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get k∈m¹ ≡ get k∈m²
    
  infixl 40 _⊂_∣_
  _⊂_∣_ : M → M → (A → Set) → Set
  _⊂_∣_ m₀ m₁ c = ∀ {𝑘} → c 𝑘 → (𝑘∈m₀ : 𝑘 ∈ m₀) → ∃ λ (𝑘∈m₁ : 𝑘 ∈ m₁) → get 𝑘∈m₀ ≡ get 𝑘∈m₁

  postulate
    put : ∀ {k₀ : A} (v₀ : V) {m₁ : M} → k₀ ∉ m₁ → ∃ λ (m₀ : M) → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get k₀∈m₀ ≡ v₀
    pick : ∀ {k₀ : A} {m₀ : M} → k₀ ∈ m₀ → ∃ λ (m₁ : M) → (m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀)

  data _⋐_ : (X : A) (ns : A) → Set where
    PureFree : (x : A) → (ns : A) → x ⋐ ns

  data _∈pf_ : (a : A) → {X : A} {ns : A} (X⋐X⋒Y : X ⋐ ns) → Set where
    singleton : (a : A) → (ns : A)→ a ∈pf PureFree a ns
    
  getpf : ∀ {a : A} {X : A} {ns : A}  {X⋐X⋒Y : X ⋐ ns} → (a ∈pf X⋐X⋒Y) → A
  getpf (singleton a ns) = ns

  reduce-PureFree-to-map' : ∀
    {PAT : A}
    {ns : A}
    (PAT⋐PAT⋒EXP : PAT ⋐ ns)
    → Dec $ ∃ λ (binding : M) → ∀ {a} (a∈binding : a ∈ binding) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PAT⋐PAT⋒EXP) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
  reduce-PureFree-to-map' (PureFree x ns) =
    yes $
      (proj₁ $ put {k₀ = x} ns {m₁ = ∅} ∅-is-empty) ,
       (λ {a∈binding → helper2 a∈binding})
 {-      
      (λ { {a} a∈binding → case IsDecEquivalence._≟_ isDecEquivalence/A x a of
        (λ
        { (yes p) → subst _ (sym p) (singleton a ns) ,
                    (let s1 , s2 , s3
                                        = put {k₀ = a} ns {m₁ = ∅} ∅-is-empty
                      in trans (get-is-unique a∈binding (subst _ (sym p) s2)) (subst _ (sym p) s3)
                    )
        ; (no ¬p) → {!!} })
        })
 -}        
{-
/home/martin/Desktop/Sandbox.agda:1121,141-159
Cannot instantiate the metavariable _3268 to solution get (subst (λ
v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥) (sym p)
(proj₁ (proj₂ (put (free g ns) ∅-is-empty)))) ≡ _k_3215 x g ns
a∈binding p since it contains the variable p which is not in scope
of the metavariable or irrelevant in the metavariable but relevant
in the solution
when checking that the expression subst _ (sym p) s3 has type
get
(subst
 (λ v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥)
 (sym p) (proj₁ (proj₂ (put (free g ns) ∅-is-empty))))
≡ _k_3215 x g ns a∈binding p
-}
      where
    helper2 : ∀
      {x : A}
      {ns : A}
      → ∀ {a} (a∈binding : a ∈ proj₁ (put {k₀ = x} ns {m₁ = ∅} ∅-is-empty)) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PureFree x ns) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
    helper2 {x₁} {ns₁} {a} a∈binding with (IsDecEquivalence._≟_ isDecEquivalence/A)  x₁ a
    helper2 {a}  {ns₁} {.a} a∈binding | yes refl = (singleton a ns₁) , (let (s1 , s2 , s3) = (put  {k₀ = a} ns₁ {m₁ = ∅} ∅-is-empty) in trans (get-is-unique a∈binding s2) s3)
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ with pick a∈binding
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ | _ , k≢a→k∈m1→Σ = let s1 , s2 , s3 = put {k₀ = x₁} ns₁ {m₁ = ∅} ∅-is-empty in contradiction ∅-is-empty (proj₁ (k≢a→k∈m1→Σ a≢x₁ s2))

module OscarMetaProblem'ₐ where
  open import Data.List.Base
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Sum
  open import Data.Product
  open import Function
  open import Data.Nat.Base hiding (_≟_; suc)
  open import Data.Empty
  open import Relation.Binary.Core using (_≡_ ; _≢_)
  open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Function using (_$_ ; case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence ; Rel)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl)

  postulate
    A : Set
    
  postulate
    M : Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_

  postulate
    ∅ : M
    _∉_ : A → M → Set
    ∅-is-empty : ∀ {𝑘} {∅ : M} → 𝑘 ∉ ∅
    
  _∈_ : A → M → Set
  _∈_ k m = ¬ k ∉ m

  postulate
    get : ∀ {k : A} {m : M} → k ∈ m → A
    get-is-unique : ∀ {k : A} {m : M} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get k∈m¹ ≡ get k∈m²
    
  infixl 40 _⊂_∣_
  _⊂_∣_ : M → M → (A → Set) → Set
  _⊂_∣_ m₀ m₁ c = ∀ {𝑘} → c 𝑘 → (𝑘∈m₀ : 𝑘 ∈ m₀) → ∃ λ (𝑘∈m₁ : 𝑘 ∈ m₁) → get 𝑘∈m₀ ≡ get 𝑘∈m₁

  postulate
    put : ∀ {k₀ : A} (v₀ : A) {m₁ : M} → k₀ ∉ m₁ → ∃ λ (m₀ : M) → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get k₀∈m₀ ≡ v₀
    pick : ∀ {k₀ : A} {m₀ : M} → k₀ ∈ m₀ → ∃ λ (m₁ : M) → (m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀)

  data _⋐_ : (X : A) (ns : A) → Set where
    PureFree : (x : A) → (ns : A) → x ⋐ ns

  data _∈pf_ : (a : A) → {X : A} {ns : A} (X⋐X⋒Y : X ⋐ ns) → Set where
    singleton : (a : A) → (ns : A)→ a ∈pf PureFree a ns
    
  getpf : ∀ {a : A} {X : A} {ns : A}  {X⋐X⋒Y : X ⋐ ns} → (a ∈pf X⋐X⋒Y) → A
  getpf (singleton a ns) = ns

  reduce-PureFree-to-map' : ∀
    {PAT : A}
    {ns : A}
    (PAT⋐PAT⋒EXP : PAT ⋐ ns)
    → Dec $ ∃ λ (binding : M) → ∀ {a} (a∈binding : a ∈ binding) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PAT⋐PAT⋒EXP) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
  reduce-PureFree-to-map' (PureFree x ns) =
    yes $
      (proj₁ $ put {k₀ = x} ns {m₁ = ∅} ∅-is-empty) ,
       (λ {a∈binding → helper2 a∈binding})
 {-      
      (λ { {a} a∈binding → case IsDecEquivalence._≟_ isDecEquivalence/A x a of
        (λ
        { (yes p) → subst _ (sym p) (singleton a ns) ,
                    (let s1 , s2 , s3
                                        = put {k₀ = a} ns {m₁ = ∅} ∅-is-empty
                      in trans (get-is-unique a∈binding (subst _ (sym p) s2)) (subst _ (sym p) s3)
                    )
        ; (no ¬p) → {!!} })
        })
 -}        
{-
/home/martin/Desktop/Sandbox.agda:1121,141-159
Cannot instantiate the metavariable _3268 to solution get (subst (λ
v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥) (sym p)
(proj₁ (proj₂ (put (free g ns) ∅-is-empty)))) ≡ _k_3215 x g ns
a∈binding p since it contains the variable p which is not in scope
of the metavariable or irrelevant in the metavariable but relevant
in the solution
when checking that the expression subst _ (sym p) s3 has type
get
(subst
 (λ v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥)
 (sym p) (proj₁ (proj₂ (put (free g ns) ∅-is-empty))))
≡ _k_3215 x g ns a∈binding p
-}
      where
    helper2 : ∀
      {x : A}
      {ns : A}
      → ∀ {a} (a∈binding : a ∈ proj₁ (put {k₀ = x} ns {m₁ = ∅} ∅-is-empty)) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PureFree x ns) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
    helper2 {x₁} {ns₁} {a} a∈binding with (IsDecEquivalence._≟_ isDecEquivalence/A)  x₁ a
    helper2 {a}  {ns₁} {.a} a∈binding | yes refl = (singleton a ns₁) , (let (s1 , s2 , s3) = (put  {k₀ = a} ns₁ {m₁ = ∅} ∅-is-empty) in trans (get-is-unique a∈binding s2) s3)
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ with pick a∈binding
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ | _ , k≢a→k∈m1→Σ = let s1 , s2 , s3 = put {k₀ = x₁} ns₁ {m₁ = ∅} ∅-is-empty in contradiction ∅-is-empty (proj₁ (k≢a→k∈m1→Σ a≢x₁ s2))

module OscarMetaProblem'ₑ where
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Sum
  open import Data.Product
  open import Function
  open import Data.Nat.Base hiding (_≟_; suc)
  open import Data.Empty
  open import Relation.Binary.Core using (_≡_ ; _≢_)
  open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Function using (_$_ ; case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence ; Rel)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl)

  postulate
    A : Set
    M : Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_
    ∅ : M
    _∉_ : A → M → Set
    ∅-is-empty : ∀ {𝑘} {∅ : M} → 𝑘 ∉ ∅
    
  _∈_ : A → M → Set
  _∈_ k m = ¬ k ∉ m

  postulate
    get : ∀ {k : A} {m : M} → k ∈ m → A
    get-is-unique : ∀ {k : A} {m : M} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get k∈m¹ ≡ get k∈m²
    
  infixl 40 _⊂_∣_
  _⊂_∣_ : M → M → (A → Set) → Set
  _⊂_∣_ m₀ m₁ c = ∀ {𝑘} → c 𝑘 → (𝑘∈m₀ : 𝑘 ∈ m₀) → ∃ λ (𝑘∈m₁ : 𝑘 ∈ m₁) → get 𝑘∈m₀ ≡ get 𝑘∈m₁

  postulate
    put : ∀ {k₀ : A} (v₀ : A) {m₁ : M} → k₀ ∉ m₁ → ∃ λ (m₀ : M) → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get k₀∈m₀ ≡ v₀
    pick : ∀ {k₀ : A} {m₀ : M} → k₀ ∈ m₀ → ∃ λ (m₁ : M) → (m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀)

  data _⋐_ : (X : A) (ns : A) → Set where
    PureFree : (x : A) → (ns : A) → x ⋐ ns

  data _∈pf_ : (a : A) → {X : A} {ns : A} (X⋐X⋒Y : X ⋐ ns) → Set where
    singleton : (a : A) → (ns : A)→ a ∈pf PureFree a ns
    
  getpf : ∀ {a : A} {X : A} {ns : A}  {X⋐X⋒Y : X ⋐ ns} → (a ∈pf X⋐X⋒Y) → A
  getpf (singleton a ns) = ns

  open IsDecEquivalence isDecEquivalence/A using (_≟_)

  reduce-PureFree-to-map' : ∀
    {PAT : A}
    {ns : A}
    (PAT⋐PAT⋒EXP : PAT ⋐ ns)
    → Dec $ ∃ λ (binding : M) → ∀ {a} (a∈binding : a ∈ binding) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PAT⋐PAT⋒EXP) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
  reduce-PureFree-to-map' (PureFree x ns) =
    yes $
      (proj₁ $ put {k₀ = x} ns {m₁ = ∅} ∅-is-empty) ,
       (λ {a∈binding → helper2 a∈binding})
 {-      
      (λ { {a} a∈binding → case x ≟ a of
        (λ
        { (yes p) → subst _ (sym p) (singleton a ns) ,
                    (let s1 , s2 , s3
                                        = put {k₀ = a} ns {m₁ = ∅} ∅-is-empty
                      in trans (get-is-unique a∈binding (subst _ (sym p) s2)) (subst _ (sym p) s3)
                    )
        ; (no ¬p) → {!!} })
        })
 -}        
{-
/home/martin/Desktop/Sandbox.agda:1121,141-159
Cannot instantiate the metavariable _3268 to solution get (subst (λ
v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥) (sym p)
(proj₁ (proj₂ (put (free g ns) ∅-is-empty)))) ≡ _k_3215 x g ns
a∈binding p since it contains the variable p which is not in scope
of the metavariable or irrelevant in the metavariable but relevant
in the solution
when checking that the expression subst _ (sym p) s3 has type
get
(subst
 (λ v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥)
 (sym p) (proj₁ (proj₂ (put (free g ns) ∅-is-empty))))
≡ _k_3215 x g ns a∈binding p
-}
      where
    helper2 : ∀
      {x : A}
      {ns : A}
      → ∀ {a} (a∈binding : a ∈ proj₁ (put {k₀ = x} ns {m₁ = ∅} ∅-is-empty)) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PureFree x ns) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
    helper2 {x₁} {ns₁} {a} a∈binding with x₁ ≟ a
    helper2 {a}  {ns₁} {.a} a∈binding | yes refl = (singleton a ns₁) , (let (s1 , s2 , s3) = (put  {k₀ = a} ns₁ {m₁ = ∅} ∅-is-empty) in trans (get-is-unique a∈binding s2) s3)
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ with pick a∈binding
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ | _ , k≢a→k∈m1→Σ = let s1 , s2 , s3 = put {k₀ = x₁} ns₁ {m₁ = ∅} ∅-is-empty in contradiction ∅-is-empty (proj₁ (k≢a→k∈m1→Σ a≢x₁ s2))

module OscarMetaProblem'ₕ where
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Sum
  open import Data.Product
  open import Function
  open import Data.Nat.Base hiding (_≟_; suc)
  open import Data.Empty
  open import Relation.Binary.Core using (_≡_ ; _≢_)
  open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Function using (_$_ ; case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence ; Rel)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl)

  postulate
    A : Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_
    ∅ : A
    _∉_ : A → A → Set
    ∅-is-empty : ∀ {𝑘 ∅} → 𝑘 ∉ ∅
    
  _∈_ : A → A → Set
  _∈_ k m = ¬ k ∉ m

  postulate
    get : ∀ {k m} → k ∈ m → A
    get-is-unique : ∀ {k m} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get k∈m¹ ≡ get k∈m²
    
  infixl 40 _⊂_∣_
  _⊂_∣_ : A → A → (A → Set) → Set
  _⊂_∣_ m₀ m₁ c = ∀ {𝑘} → c 𝑘 → (𝑘∈m₀ : 𝑘 ∈ m₀) → ∃ λ (𝑘∈m₁ : 𝑘 ∈ m₁) → get 𝑘∈m₀ ≡ get 𝑘∈m₁

  postulate
    put : ∀ {k₀} (v₀ : A) → ∃ λ m₀ → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get k₀∈m₀ ≡ v₀
    pick : ∀ {k₀ m₀} → k₀ ∈ m₀ → ∃ λ (m₁ : A) → (m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀)

  data _⋐_ : (X : A) (ns : A) → Set where
    PureFree : (x : A) → (ns : A) → x ⋐ ns

  data _∈pf_ : (a : A) → {X : A} {ns : A} (X⋐X⋒Y : X ⋐ ns) → Set where
    singleton : (a : A) → (ns : A)→ a ∈pf PureFree a ns
    
  getpf : ∀ {a : A} {X : A} {ns : A}  {X⋐X⋒Y : X ⋐ ns} → (a ∈pf X⋐X⋒Y) → A
  getpf (singleton a ns) = ns

  open IsDecEquivalence isDecEquivalence/A using (_≟_)

  reduce-PureFree-to-map' : ∀
    {PAT : A}
    {ns : A}
    (PAT⋐PAT⋒EXP : PAT ⋐ ns)
    → Dec $ ∃ λ binding → ∀ {a} (a∈binding : a ∈ binding) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PAT⋐PAT⋒EXP) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
  reduce-PureFree-to-map' (PureFree x ns) =
    yes $
      (proj₁ $ put {k₀ = x} ns) ,
       (λ {a∈binding → helper2 a∈binding})
 {-      
      (λ { {a} a∈binding → case x ≟ a of
        (λ
        { (yes p) → subst _ (sym p) (singleton a ns) ,
                    (let s1 , s2 , s3
                                        = put {k₀ = a} ns
                      in trans (get-is-unique a∈binding (subst _ (sym p) s2)) (subst _ (sym p) s3)
                    )
        ; (no ¬p) → {!!} })
        })
 -}        
{-
/home/martin/Desktop/Sandbox.agda:1121,141-159
Cannot instantiate the metavariable _3268 to solution get (subst (λ
v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥) (sym p)
(proj₁ (proj₂ (put (free g ns) ∅-is-empty)))) ≡ _k_3215 x g ns
a∈binding p since it contains the variable p which is not in scope
of the metavariable or irrelevant in the metavariable but relevant
in the solution
when checking that the expression subst _ (sym p) s3 has type
get
(subst
 (λ v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥)
 (sym p) (proj₁ (proj₂ (put (free g ns) ∅-is-empty))))
≡ _k_3215 x g ns a∈binding p
-}
      where
    helper2 : ∀
      {x : A}
      {ns : A}
      → ∀ {a} (a∈binding : a ∈ proj₁ (put {k₀ = x} ns)) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PureFree x ns) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP
    helper2 {x₁} {ns₁} {a} a∈binding with x₁ ≟ a
    helper2 {a}  {ns₁} {.a} a∈binding | yes refl = (singleton a ns₁) , (let (s1 , s2 , s3) = (put  {k₀ = a} ns₁) in trans (get-is-unique a∈binding s2) s3)
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ with pick a∈binding
    helper2 {x₁} {ns₁} {a} a∈binding | no a≢x₁ | _ , k≢a→k∈m1→Σ = let s1 , s2 , s3 = put {k₀ = x₁} ns₁ in contradiction ∅-is-empty (proj₁ (k≢a→k∈m1→Σ a≢x₁ s2))

module OscarMetaProblem'ᵢ where
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Sum
  open import Data.Product
  open import Function
  open import Data.Nat.Base hiding (_≟_; suc)
  open import Data.Empty
  open import Relation.Binary.Core using (_≡_ ; _≢_)
  open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Function using (_$_ ; case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence ; Rel)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl)

  postulate
    A : Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_
    ∅ : A
    _∉_ : A → A → Set
    
  _∈_ : A → A → Set
  _∈_ k m = ¬ k ∉ m

  postulate
    get∈ : ∀ {k m} → k ∈ m → A
    get-is-unique : ∀ {k m} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get∈ k∈m¹ ≡ get∈ k∈m²
    put : (k₀ : A) (v₀ : A) → ∃ λ m₀ → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get∈ k₀∈m₀ ≡ v₀

  data _⋐_ : (b c : A) → Set where
    C : (b : A) → (c : A) → b ⋐ c

  data _≺_ : (a : A) → {b : A} {c : A} (b⋐c : b ⋐ c) → Set where
    E : (b : A) → (c : A) → b ≺ C b c
    
  get≺ : ∀ {a b c : A} {b⋐c : b ⋐ c} → (a ≺ b⋐c) → A
  get≺ (E _ c) = c

  open IsDecEquivalence isDecEquivalence/A using (_≟_)

  reduce-PureFree-to-map' : ∀
    {b : A}
    {c : A}
    (b⋐c : b ⋐ c)
    → Dec $ ∃ λ m → ∀ {k} (k∈m : k ∈ m) → ∃ λ (k≺b⋐c : k ≺ b⋐c) → get∈ k∈m ≡ get≺ k≺b⋐c
  reduce-PureFree-to-map' (C b c) =
    yes $
      (proj₁ $ put b c) ,
      (λ {a∈binding → helper2 a∈binding})
 {-      
      (λ { {a} a∈binding → case b ≟ a of
        (λ
        { (yes p) → subst _ (sym p) (E a c) ,
                    (let s1 , s2 , s3 = put a c in trans (get-is-unique a∈binding (subst _ (sym p) s2)) (subst _ (sym p) s3))
        ; (no ¬p) → {!!}
        })
      })
 -}        
{-
/home/martin/Desktop/Sandbox.agda:1121,141-159
Cannot instantiate the metavariable _3268 to solution get (subst (λ
v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥) (sym p)
(proj₁ (proj₂ (put (free g ns) ∅-is-empty)))) ≡ _k_3215 x g ns
a∈binding p since it contains the variable p which is not in scope
of the metavariable or irrelevant in the metavariable but relevant
in the solution
when checking that the expression subst _ (sym p) s3 has type
get
(subst
 (λ v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥)
 (sym p) (proj₁ (proj₂ (put (free g ns) ∅-is-empty))))
≡ _k_3215 x g ns a∈binding p
-}
      where
    helper2 : ∀
      {k : A}
      {m : A}
      → ∀ {x} (x∈km : x ∈ proj₁ (put k m)) → ∃ λ (x≺Ckm : x ≺ C k m) → get∈ x∈km ≡ get≺ x≺Ckm
    helper2 {k} {_} {x} _ with k ≟ x
    helper2 {k}  {m} {.k} k∈km | yes refl = (E k m) , (let (s1 , s2 , s3) = (put k m) in trans (get-is-unique k∈km s2) s3)
    helper2 {_} {_} {_} _ | no _ = {!!}

module OscarMetaProblem'ⱼ where
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Product
  open import Function
  open import Data.Nat.Base hiding (_≟_; suc)
  open import Data.Empty
  open import Relation.Binary.Core using (_≡_ ; _≢_)
  open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Function using (_$_ ; case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl)

  postulate
    A : Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_
    ∅ : A
    _∉_ : A → A → Set
    
  _∈_ : A → A → Set
  _∈_ k m = ¬ k ∉ m

  postulate
    get∈ : ∀ {k m} → k ∈ m → A
    get-is-unique : ∀ {k m} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get∈ k∈m¹ ≡ get∈ k∈m²
    put : (k₀ : A) (v₀ : A) → ∃ λ m₀ → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get∈ k₀∈m₀ ≡ v₀

  data _⋐_ : (b c : A) → Set where
    C : (b : A) → (c : A) → b ⋐ c

  data _≺_ : (a : A) → {b : A} {c : A} (b⋐c : b ⋐ c) → Set where
    E : (b : A) → (c : A) → b ≺ C b c
    
  get≺ : ∀ {a b c : A} {b⋐c : b ⋐ c} → (a ≺ b⋐c) → A
  get≺ (E _ c) = c

  open IsDecEquivalence isDecEquivalence/A using (_≟_)

  foo : ∀
    {b : A}
    {c : A}
    (b⋐c : b ⋐ c)
    → ∃ λ m → ∀ {k} (k∈m : k ∈ m) → ∃ λ (k≺b⋐c : k ≺ b⋐c) → get∈ k∈m ≡ get≺ k≺b⋐c
  foo (C b c) = 
      (proj₁ $ put b c) ,
      (λ {x∈km → helper x∈km})
 {-      
      (λ { {x} x∈km → case b ≟ x of
        (λ
        { (yes p) → subst _ (sym p) (E x c) ,
                    (let s1 , s2 , s3 = put x c in trans (get-is-unique x∈km (subst _ (sym p) s2)) {!(subst _ (sym p) s3)!})
        ; (no ¬p) → {!!}
        })
      })
 -}
 
{-
/home/martin/Desktop/Sandbox.agda:1121,141-159
Cannot instantiate the metavariable _3268 to solution get (subst (λ
v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥) (sym p)
(proj₁ (proj₂ (put (free g ns) ∅-is-empty)))) ≡ _k_3215 x g ns
a∈binding p since it contains the variable p which is not in scope
of the metavariable or irrelevant in the metavariable but relevant
in the solution
when checking that the expression subst _ (sym p) s3 has type
get
(subst
 (λ v → a ∉ ((λ r → proj₁ r) $ put (free g ns) ∅-is-empty) → ⊥)
 (sym p) (proj₁ (proj₂ (put (free g ns) ∅-is-empty))))
≡ _k_3215 x g ns a∈binding p
-}

      where
    helper : ∀
      {k : A}
      {m : A}
      → ∀ {x} (x∈km : x ∈ proj₁ (put k m)) → ∃ λ (x≺Ckm : x ≺ C k m) → get∈ x∈km ≡ get≺ x≺Ckm
    helper {k} {_} {x} _ with k ≟ x
    helper {k}  {m} {.k} k∈km | yes refl = (E k m) , (let (s1 , s2 , s3) = (put k m) in trans (get-is-unique k∈km s2) s3)
    helper {_} {_} {_} _ | no _ = {!!}

module OscarMetaProblem'ₖ where
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Product
  open import Function
  open import Data.Nat.Base hiding (_≟_; suc)
  open import Data.Empty
  open import Relation.Binary.Core using (_≡_ ; _≢_)
  open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Function using (_$_ ; case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl)

  postulate
    A : Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_
    ∅ : A
    _∉_ : A → A → Set
    
  _∈_ : A → A → Set
  _∈_ k m = ¬ k ∉ m

  postulate
    get∈ : ∀ {k m} → k ∈ m → A
    get-is-unique : ∀ {k m} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get∈ k∈m¹ ≡ get∈ k∈m²
    put : (k₀ : A) (v₀ : A) → ∃ λ m₀ → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get∈ k₀∈m₀ ≡ v₀

  data _⋐_ : (b c : A) → Set where
    C : (b : A) → (c : A) → b ⋐ c

  data _≺_ : (a : A) → {b : A} {c : A} (b⋐c : b ⋐ c) → Set where
    E : (b : A) → (c : A) → b ≺ C b c
    
  get≺ : ∀ {a b c : A} {b⋐c : b ⋐ c} → (a ≺ b⋐c) → A
  get≺ (E _ c) = c

  open IsDecEquivalence isDecEquivalence/A using (_≟_)

  foo :
    (b c : A) →
    ∀ {k}
    → (k∈m : k ∈ proj₁ (put b c)) → ∃ λ (k≺b⋐c : k ≺ C b c) → get∈ k∈m ≡ get≺ k≺b⋐c
  foo b c {x} x∈km =
    helper x∈km
--    case b ≟ x of λ
--      { (yes p) → subst _ (sym p) (E x c) ,
--                  (let s1 , s2 , s3 = put x c in trans (get-is-unique x∈km (subst _ (sym p) s2)) (subst _ (sym p) s3))
--      ; (no ¬p) → {!!}
--      }
 
{-
/home/martin/Desktop/Sandbox.agda:2640,101-119
Cannot instantiate the metavariable _6711 to solution get∈ (subst
(λ v → x ∉ proj₁ (put v c) → ⊥) (sym p) (proj₁ (proj₂ (put x c))))
≡ _k_6685 b c x∈km p since it contains the variable p which is not
in scope of the metavariable or irrelevant in the metavariable but
relevant in the solution
when checking that the expression subst _ (sym p) s3 has type
get∈
(subst (λ v → x ∉ proj₁ (put v c) → ⊥) (sym p)
 (proj₁ (proj₂ (put x c))))
≡ _k_6685 b c x∈km p
-}

      where
    helper : ∀
      {k : A}
      {m : A}
      → ∀ {x} (x∈km : x ∈ proj₁ (put k m)) → ∃ λ (x≺Ckm : x ≺ C k m) → get∈ x∈km ≡ get≺ x≺Ckm
    helper {k} {_} {x} _ with k ≟ x
    helper {k}  {m} {.k} k∈km | yes refl = (E k m) , (let (s1 , s2 , s3) = (put k m) in trans (get-is-unique k∈km s2) s3)
    helper {_} {_} {_} _ | no _ = {!!}

module OscarMetaProblem'ₗ where
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Product
  open import Function
  open import Data.Nat.Base hiding (_≟_; suc)
  open import Data.Empty
  open import Relation.Binary.Core using (_≡_ ; _≢_)
  open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Function using (_$_ ; case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl)

  postulate
    A : Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_
    _∈_ : A → A → Set
    get∈ : ∀ {k m} → k ∈ m → A
    get-is-unique : ∀ {k m} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get∈ k∈m¹ ≡ get∈ k∈m²
    put : (k₀ : A) (v₀ : A) → ∃ λ m₀ → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get∈ k₀∈m₀ ≡ v₀

  data _⋐_ : (b c : A) → Set where
    C : (b : A) → (c : A) → b ⋐ c

  data _≺_ : (a : A) → {b : A} {c : A} (b⋐c : b ⋐ c) → Set where
    E : (b : A) → (c : A) → b ≺ C b c
    
  get≺ : ∀ {a b c : A} {b⋐c : b ⋐ c} → (a ≺ b⋐c) → A
  get≺ (E _ c) = c

  open IsDecEquivalence isDecEquivalence/A using (_≟_)

  foo : ∀
    {a} 
    (b c : A)
    (a∈b⟫c : a ∈ proj₁ (put b c))
    → ∃ λ (a≺b⋐c : a ≺ C b c) → get∈ a∈b⟫c ≡ get≺ a≺b⋐c
  foo {a} b c a∈b⟫c =
    helper a∈b⟫c
--    case a ≟ b of λ
--    { (yes a≡b) → subst _ a≡b (E a c) ,
--                  (let _ , a∈c , get∈a∈c = put a c in trans (get-is-unique a∈b⟫c (subst _ a≡b a∈c)) (subst _ a≡b get∈a∈c))
--    ; (no a≢b) → {!!}
--    }
 
{-
/home/martin/Desktop/Sandbox.agda:2640,101-119
Cannot instantiate the metavariable _6711 to solution get∈ (subst
(λ v → x ∉ proj₁ (put v c) → ⊥) (sym p) (proj₁ (proj₂ (put x c))))
≡ _k_6685 b c x∈km p since it contains the variable p which is not
in scope of the metavariable or irrelevant in the metavariable but
relevant in the solution
when checking that the expression subst _ (sym p) s3 has type
get∈
(subst (λ v → x ∉ proj₁ (put v c) → ⊥) (sym p)
 (proj₁ (proj₂ (put x c))))
≡ _k_6685 b c x∈km p
-}

      where
    helper : ∀
      {a b c}
      (a∈b⟫c : a ∈ proj₁ (put b c)) → ∃ λ (a≺Cbc : a ≺ C b c) → get∈ a∈b⟫c ≡ get≺ a≺Cbc
    helper {a} {b}  {_}  _ with a ≟ b
    helper {.a} {a} {c} a∈a⟫c | yes refl = (E a c) , (let (_ , a∈a⟫c₂ , s3) = (put a c) in trans (get-is-unique a∈a⟫c a∈a⟫c₂) s3)
    helper {_} {_}  {_} _ | no _ = {!!}

module OscarMetaProblem'ₘ where
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Product
  open import Function
  open import Data.Nat.Base hiding (_≟_; suc)
  open import Data.Empty
  open import Relation.Binary.Core using (_≡_ ; _≢_)
  open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Function using (_$_ ; case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl)

  postulate
    A : Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_
    _∈_ : A → A → Set
    get∈ : ∀ {k m} → k ∈ m → A
    get-is-unique : ∀ {k m} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get∈ k∈m¹ ≡ get∈ k∈m²
    put : (k₀ : A) (v₀ : A) → ∃ λ m₀ → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get∈ k₀∈m₀ ≡ v₀

  data _⋐_ : (b c : A) → Set where
    C : (b : A) → (c : A) → b ⋐ c

  data _≺_ : (a : A) → {b : A} {c : A} (b⋐c : b ⋐ c) → Set where
    E : (b : A) → (c : A) → b ≺ C b c
    
  get≺ : ∀ {a b c : A} {b⋐c : b ⋐ c} → (a ≺ b⋐c) → A
  get≺ (E _ c) = c

  open IsDecEquivalence isDecEquivalence/A using (_≟_)

  foo : ∀
    {a} 
    (b c : A)
    (a∈b⟫c : a ∈ proj₁ (put b c))
    (a≡b : a ≡ b)
    → ∃ λ (a≺b⋐c : a ≺ C b c) → get∈ a∈b⟫c ≡ get≺ a≺b⋐c
  foo {a} b c a∈b⟫c a≡b =
    helper a∈b⟫c a≡b
--    subst _ a≡b (E a c) ,
--    (let _ , a∈c , get∈a∈c = put a c in trans (get-is-unique a∈b⟫c (subst _ a≡b a∈c)) (subst _ a≡b get∈a∈c))
 
{-
/home/martin/Desktop/Sandbox.agda:2640,101-119
Cannot instantiate the metavariable _6711 to solution get∈ (subst
(λ v → x ∉ proj₁ (put v c) → ⊥) (sym p) (proj₁ (proj₂ (put x c))))
≡ _k_6685 b c x∈km p since it contains the variable p which is not
in scope of the metavariable or irrelevant in the metavariable but
relevant in the solution
when checking that the expression subst _ (sym p) s3 has type
get∈
(subst (λ v → x ∉ proj₁ (put v c) → ⊥) (sym p)
 (proj₁ (proj₂ (put x c))))
≡ _k_6685 b c x∈km p
-}

      where
    helper : ∀
      {a b c}
      (a∈b⟫c : a ∈ proj₁ (put b c))
      (a≡b : a ≡ b)
      → ∃ λ (a≺Cbc : a ≺ C b c) → get∈ a∈b⟫c ≡ get≺ a≺Cbc
    helper {.a} {a} {c} a∈a⟫c refl = (E a c) , (let (_ , a∈a⟫c₂ , s3) = (put a c) in trans (get-is-unique a∈a⟫c a∈a⟫c₂) s3)

module OscarMetaProblem'ₙ where
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Data.Product
  open import Function
  open import Data.Nat.Base hiding (_≟_; suc)
  open import Data.Empty
  open import Relation.Binary.Core using (_≡_ ; _≢_)
  open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Data.Nat.Base using (ℕ ; suc)
  open import Function using (_$_ ; case_of_)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary using (IsDecEquivalence)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl)

  postulate
    A : Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_
    _∈_ : A → A → Set
    get∈ : ∀ {k m} → k ∈ m → A
    get-is-unique : ∀ {k m} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get∈ k∈m¹ ≡ get∈ k∈m²
    put : (k₀ : A) (v₀ : A) → ∃ λ m₀ → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get∈ k₀∈m₀ ≡ v₀

  data _⋐_ : (b c : A) → Set where
    C : (b : A) → (c : A) → b ⋐ c

  data _≺_ : (a : A) → {b : A} {c : A} (b⋐c : b ⋐ c) → Set where
    E : (b : A) → (c : A) → b ≺ C b c
    
  get≺ : ∀ {a b c : A} {b⋐c : b ⋐ c} → (a ≺ b⋐c) → A
  get≺ (E _ c) = c

  open IsDecEquivalence isDecEquivalence/A using (_≟_)

  bar :
    (a b c : A)
    (a∈b⟫c : a ∈ proj₁ (put b c))
    (a≡b : a ≡ b)
    → get∈ a∈b⟫c ≡ get≺ {a} {b⋐c = C b c} (subst _ a≡b (E a c))
  bar a .a c a∈a⟫c refl = (let (_ , a∈a⟫c₂ , s3) = (put a c) in trans (get-is-unique a∈a⟫c a∈a⟫c₂) s3)
    
  foo :
    (a b c : A)
    (a∈b⟫c : a ∈ proj₁ (put b c))
    (a≡b : a ≡ b)
    → get∈ a∈b⟫c ≡ get≺ {a} {b⋐c = C b c} (subst _ a≡b (E a c))
  foo a b c a∈b⟫c a≡b =
    bar a b c a∈b⟫c a≡b
--    (let _ , a∈a⟫c₂ , get∈a∈c = put a c in trans (get-is-unique a∈b⟫c (subst _ a≡b a∈a⟫c₂)) (subst _ a≡b get∈a∈c))
 
{-
/home/martin/Desktop/Sandbox.agda:2640,101-119
Cannot instantiate the metavariable _6711 to solution get∈ (subst
(λ v → x ∉ proj₁ (put v c) → ⊥) (sym p) (proj₁ (proj₂ (put x c))))
≡ _k_6685 b c x∈km p since it contains the variable p which is not
in scope of the metavariable or irrelevant in the metavariable but
relevant in the solution
when checking that the expression subst _ (sym p) s3 has type
get∈
(subst (λ v → x ∉ proj₁ (put v c) → ⊥) (sym p)
 (proj₁ (proj₂ (put x c))))
≡ _k_6685 b c x∈km p
-}

module OscarMetaProblem'ₒ where
  open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
  open import Relation.Binary using (IsDecEquivalence)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; trans ; refl)

  postulate
    A : Set
    isDecEquivalence/A : IsDecEquivalence {A = A} _≡_
    _∈_ : A → A → Set
    get∈ : ∀ {k m} → k ∈ m → A
    get-is-unique : ∀ {k m} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get∈ k∈m¹ ≡ get∈ k∈m²
    put : (k₀ : A) (v₀ : A) → ∃ λ m₀ → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get∈ k₀∈m₀ ≡ v₀

  data _⋐_ : (b c : A) → Set where
    C : (b : A) → (c : A) → b ⋐ c

  data _≺_ : (a : A) → {b : A} {c : A} (b⋐c : b ⋐ c) → Set where
    E : (b : A) → (c : A) → b ≺ C b c
    
  get≺ : ∀ {a b c : A} {b⋐c : b ⋐ c} → (a ≺ b⋐c) → A
  get≺ (E _ c) = c

  open IsDecEquivalence isDecEquivalence/A using (_≟_)

  bar :
    (a b c : A)
    (a∈b⟫c : a ∈ proj₁ (put b c))
    (a≡b : a ≡ b)
    → get∈ a∈b⟫c ≡ get≺ {a} {b⋐c = C b c} (subst _ a≡b (E a c))
  bar a .a c a∈a⟫c refl =
    let (_ , a∈a⟫c₂ , s3) = (put a c) in trans (get-is-unique a∈a⟫c a∈a⟫c₂) s3
    
  foo :
    (a b c : A)
    (a∈b⟫c : a ∈ proj₁ (put b c))
    (a≡b : a ≡ b)
    → get∈ a∈b⟫c ≡ get≺ {a} {b⋐c = C b c} (subst _ a≡b (E a c))
  foo a b c a∈b⟫c a≡b =
    bar a b c a∈b⟫c a≡b
--    let _ , a∈a⟫c₂ , get∈a∈c = put a c in trans (get-is-unique a∈b⟫c (subst _ a≡b a∈a⟫c₂)) (subst _ a≡b get∈a∈c)
 
{-
/home/martin/Desktop/Sandbox.agda:2640,101-119
Cannot instantiate the metavariable _6711 to solution get∈ (subst
(λ v → x ∉ proj₁ (put v c) → ⊥) (sym p) (proj₁ (proj₂ (put x c))))
≡ _k_6685 b c x∈km p since it contains the variable p which is not
in scope of the metavariable or irrelevant in the metavariable but
relevant in the solution
when checking that the expression subst _ (sym p) s3 has type
get∈
(subst (λ v → x ∉ proj₁ (put v c) → ⊥) (sym p)
 (proj₁ (proj₂ (put x c))))
≡ _k_6685 b c x∈km p
-}
