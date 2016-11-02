module Reduction where
  open import Postlude
  open import Tactic.Reright
  open import Free

  postulate
    A : Set

  V : A → Set₁
  V = λ _ → Free List A

  postulate
    M : ℕ → Set₁
    isDecEquivalence/A : Eq A
    isDecEquivalence/V : {a : A} → Eq (V a)

  open import Map ⦃ isDecEquivalence/A ⦄ V ⦃ λ {a} → isDecEquivalence/V {a} ⦄ M
  postulate
    m : Map
    ∅ : M 0

  open FreeComparison {{isDecEquivalence/A}}
  open Map m renaming (get to get∈)

  record Formula where
    field
      expression : Free List A
      isFree : A → Bool

  Ornamented

  match? :
    (pat : Tree A)
    (exp : Tree A)
    (isPatVar : A → Bool)
    Dec ∃ λ (p⋐e : pat ⋐ exp) →
    → Dec ∃ λ (binding : Binding) →
          (∀ (v : A) → (v⊰p⋐e : v ⊰ p⋐e) →  ⟦ v ~ get⊰ v⊰p⋐e ∈ binding ⟧)
    {PAT EXP : Free List A}
    {PAT⋒EXP : PAT ⋒ EXP}
    (PAT⋐PAT⋒EXP : PAT ⋐ PAT⋒EXP)
    (isVar : A → Bool)
    → Dec (Match PAT⋐PAT⋒EXP isVar)
  match? = {!!}

  --     vars-in-pattern-are-also-in-binding-and-have-same-value :
  --       ∀ (v : A) → isVar v ≡ true → (v∈pfPAT⋐PAT⋒EXP : v ⊰ PAT⋐PAT⋒EXP) → v IsBoundIn binding WithValue get⊰ v∈pfPAT⋐PAT⋒EXP
  --     keys-in-binding-are-vars :
  --       ∀ (v : A) → (v∈binding : v ∈ binding) → isVar v ≡ true
  --     keys-in-binding-are-in-pattern-and-have-same-value :
  --       ∀ (v : A) → (v∈binding : v ∈ binding) → ∃ λ (v∈pfPAT⋐PAT⋒EXP : v ⊰ PAT⋐PAT⋒EXP) → get∈ v∈binding ≡ get⊰ v∈pfPAT⋐PAT⋒EXP


  -- data _⊰_ : (a : A) → {X : Free List A} {Y : Free List A} (X⋒Y : X ⋐ Y) → Set (sucₗ α) where
  --     singletonPure : (a : A) → a ⊰ Equal {X = pure a} (Pure refl)
  --     singletonFree : (a : A) → ∀ {N : Set α} → (g : N → Free List A) → (ns : List N)→ a ⊰ PureFree a g ns
  --     descend-first : {a : A} → {M N : Set α} →
  --                     {f : M → Free List A} →
  --                     {m : M} {ms : List M} →
  --                     {g : N → Free List A} →
  --                     {n : N} {ns : List N} →
  --                     (notequal : ¬ free f (m ∷ ms) ≞ free g (n ∷ ns)) →
  --                     {fm⋐first : f m ⋐ g n} →
  --                     (freefms⋐rest : free f ms ⋐ free g ns)
  --                     (a⊰first : a ⊰ fm⋐first) →
  --                     a ⊰ FreeFree notequal fm⋐first freefms⋐rest
  --     descend2 : (a : A) {M N : Set α} →
  --                {f : M → Free List A} →
  --                {m : M} {ms : List M} →
  --                {g : N → Free List A} →
  --                {n : N} {ns : List N} →
  --                {notequal : ¬ free f (m ∷ ms) ≞ free g (n ∷ ns)} →
  --                {fm⋐first : f m ⋐ g n} →
  --                {freefms⋐rest : free f ms ⋐ free g ns}
  --                (a⊰first : a ⊰ freefms⋐rest) →
  --                a ⊰ FreeFree notequal fm⋐first freefms⋐rest

  --   get⊰ : ∀ {a : A} {X : Free List A} {Y : Free List A} {X⋐Y : X ⋐ Y} → a ⊰ X⋐Y → Free List A
  --   get⊰ (singletonPure a) = pure a
  --   get⊰ (singletonFree _ g ns) = free g ns
  --   get⊰ (descend-first _ _ a⊰first) = get⊰ a⊰first
  --   get⊰ (descend2 _ x) = get⊰ x

  --   -- _⊰?_ : (a : A) {X : Free List A} {Y : Free List A} {X⋒Y : X ⋒ Y} (X⋐X⋒Y : X ⋐ X⋒Y) → Dec (a ⊰ X⋐X⋒Y)
  --   -- _⊰?_ a (Equal X≞Y) = no (λ ())
  --   -- _⊰?_ a (PureFree x g ns) with a ≟ x
  --   -- _⊰?_ a (PureFree .a g ns) | yes refl = yes (singleton a g ns)
  --   -- _⊰?_ a (PureFree  x g ns) | no a≢x = no λ { (singleton _ _ _) → a≢x refl }
  --   -- _⊰?_ a (Free∷Free∷ notequal X⋐X⋒Y X⋐X⋒Ys) with a ⊰? X⋐X⋒Y
  --   -- _⊰?_ a (Free∷Free∷ notequal X⋐X⋒Y X⋐X⋒Ys) | yes x = yes (descend1 a x)
  --   -- _⊰?_ a (Free∷Free∷ notequal X⋐X⋒Y X⋐X⋒Ys) | no x with a ⊰? X⋐X⋒Ys
  --   -- _⊰?_ a (Free∷Free∷ notequal X⋐X⋒Y X⋐X⋒Ys) | no x | yes y = yes (descend2 a y)
  --   -- _⊰?_ a (Free∷Free∷ notequal X⋐X⋒Y X⋐X⋒Ys) | no x | no y = no (λ { (descend1 _ x₁) → x x₁ ; (descend2 _ x₁) → y x₁ })

  -- Formula = Free List A
  -- IsVar = A → Bool

  -- record Binding
  --        : Set
  --        where
  --   field

  -- data Binding : Set where
  --   ⑴ : {s : ℕ} → M s → Binding

  -- record Match
  --        (pat : Formula)
  --        (exp : Formula)
  --        (isVar : IsVar)
  --        : Set₁
  --        where
  --   field
  --     binding : Binding
  --     vars-in-pattern-are-also-in-binding-and-have-same-value :
  --       ∀ (v : A) → isVar v ≡ true → (v∈pfPAT⋐PAT⋒EXP : v ⊰ PAT⋐PAT⋒EXP) → v IsBoundIn binding WithValue get⊰ v∈pfPAT⋐PAT⋒EXP
  --     keys-in-binding-are-vars :
  --       ∀ (v : A) → (v∈binding : v ∈ binding) → isVar v ≡ true
  --     keys-in-binding-are-in-pattern-and-have-same-value :
  --       ∀ (v : A) → (v∈binding : v ∈ binding) → ∃ λ (v∈pfPAT⋐PAT⋒EXP : v ⊰ PAT⋐PAT⋒EXP) → get∈ v∈binding ≡ get⊰ v∈pfPAT⋐PAT⋒EXP

  -- record ⟦_∈_=_⟧ (v : A) (binding : Binding) (value : V v) : Set where
  --   field
  --     bound : v ∈ binding
  --     valued : value ≡ get∈ bound

  -- record Match
  --          {PAT EXP : Free List A}
  --          {PAT⋒EXP : PAT ⋒ EXP}
  --          (PAT⋐PAT⋒EXP : PAT ⋐ PAT⋒EXP)
  --          (isVar : A → Bool) : Set₁
  --        where
  --   field
  --     {s} : ℕ
  --     binding : M s
  --     vars-in-pattern-are-also-in-binding-and-have-same-value :
  --       ∀ (v : A) → isVar v ≡ true → (v∈pfPAT⋐PAT⋒EXP : v ⊰ PAT⋐PAT⋒EXP) → ∃ λ (v∈binding : v ∈ binding) → get⊰ v∈pfPAT⋐PAT⋒EXP ≡ get∈ v∈binding
  --     keys-in-binding-are-vars :
  --       ∀ (v : A) → (v∈binding : v ∈ binding) → isVar v ≡ true
  --     keys-in-binding-are-in-pattern-and-have-same-value :
  --       ∀ (v : A) → (v∈binding : v ∈ binding) → ∃ λ (v∈pfPAT⋐PAT⋒EXP : v ⊰ PAT⋐PAT⋒EXP) → get∈ v∈binding ≡ get⊰ v∈pfPAT⋐PAT⋒EXP

  -- record Match'
  --          {PAT EXP : Free List A}
  --          (PAT⋐⋒EXP : PAT ⋐⋒ EXP)
  --          (isVar : A → Bool) : Set₁
  --        where
  --   field
  --     {s} : ℕ
  --     binding : M s
  --     vars-in-pattern-are-also-in-binding-and-have-same-value :
  --       ∀ (v : A) → isVar v ≡ true → (v∈pfPAT⋐PAT⋒EXP : v ⊰ PAT⋐⋒EXP) → ∃ λ (v∈binding : v ∈ binding) → get⊰ v∈pfPAT⋐PAT⋒EXP ≡ get∈ v∈binding
  --     keys-in-binding-are-vars :
  --       ∀ (v : A) → (v∈binding : v ∈ binding) → isVar v ≡ true
  --     keys-in-binding-are-in-pattern-and-have-same-value :
  --       ∀ (v : A) → (v∈binding : v ∈ binding) → ∃ λ (v∈pfPAT⋐PAT⋒EXP : v ⊰ PAT⋐⋒EXP) → get∈ v∈binding ≡ get⊰ v∈pfPAT⋐PAT⋒EXP

  -- match? : ∀
  --   {PAT EXP : Free List A}
  --   {PAT⋒EXP : PAT ⋒ EXP}
  --   (PAT⋐PAT⋒EXP : PAT ⋐ PAT⋒EXP)
  --   (isVar : A → Bool)
  --   → Dec (Match PAT⋐PAT⋒EXP isVar)
  -- match? = {!!}

  -- record SubstitutionAlt
  --          {s/map}
  --          {map : M s/map}
  --          {k : A}
  --          {l : Free List A}
  --          {s : Free List A}
  --          {l⋒s : l ⋒ s}
  --          (l⋐r : l ⋐ l⋒s)
  --          (k∈map : k ∈ map)
  --        : Set₁
  --        where
  --   field
  --     k⊰l⋐r : k ⊰ l⋐r
  --     alt4 : get⊰ k⊰l⋐r ≡ get∈ k∈map

  -- record SubstitutionLaw
  --          {s}
  --          (binding : M s)
  --          (PAT : Free List A)
  --          (isVar : A → Bool)
  --          (substitutions : Free List A)
  --          (cappers : PAT ⋒ substitutions)
  --        : Set₁
  --        where
  --   field
  --     diff2 : PAT ⋐ cappers
  --     mat : Match diff2 isVar
  --     law : Match.binding mat ⊆ binding
  --     law2 : ∀ {a} (a∈binding : a ∈ binding) → a ∉ Match.binding mat → ¬ SubstitutionAlt diff2 a∈binding

  -- record Substitution
  --          {s}
  --          (binding : M s)
  --          (PAT : Free List A)
  --          (isVar : A → Bool)
  --        : Set₁
  --        where
  --   field
  --     substitutions : Free List A
  --     lem : (cappers : PAT ⋒ substitutions) → SubstitutionLaw binding PAT isVar substitutions cappers

  -- substitute : ∀ {s} → (binding : M s) → (PAT : Free List A) → (isVar : A → Bool) → Substitution binding PAT isVar
  -- substitute = {!!}
