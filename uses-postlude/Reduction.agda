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

  record Match
           {PAT EXP : Free List A}
           {PAT⋒EXP : PAT ⋒ EXP}
           (PAT⋐PAT⋒EXP : PAT ⋐ PAT⋒EXP)
           (isVar : A → Bool) : Set₁
         where
    field
      {s} : ℕ
      binding : M s
      vars-in-pattern-are-also-in-binding-and-have-same-value :
        ∀ (v : A) → isVar v ≡ true → (v∈pfPAT⋐PAT⋒EXP : v ⊰ PAT⋐PAT⋒EXP) → ∃ λ (v∈binding : v ∈ binding) → get⊰ v∈pfPAT⋐PAT⋒EXP ≡ get∈ v∈binding
      keys-in-binding-are-vars :
        ∀ (v : A) → (v∈binding : v ∈ binding) → isVar v ≡ true
      keys-in-binding-are-in-pattern-and-have-same-value :
        ∀ (v : A) → (v∈binding : v ∈ binding) → ∃ λ (v∈pfPAT⋐PAT⋒EXP : v ⊰ PAT⋐PAT⋒EXP) → get∈ v∈binding ≡ get⊰ v∈pfPAT⋐PAT⋒EXP

  record Match'
           {PAT EXP : Free List A}
           (PAT⋐⋒EXP : PAT ⋐⋒ EXP)
           (isVar : A → Bool) : Set₁
         where
    field
      {s} : ℕ
      binding : M s
      vars-in-pattern-are-also-in-binding-and-have-same-value :
        ∀ (v : A) → isVar v ≡ true → (v∈pfPAT⋐PAT⋒EXP : v ⊰ PAT⋐⋒EXP) → ∃ λ (v∈binding : v ∈ binding) → get⊰ v∈pfPAT⋐PAT⋒EXP ≡ get∈ v∈binding
      keys-in-binding-are-vars :
        ∀ (v : A) → (v∈binding : v ∈ binding) → isVar v ≡ true
      keys-in-binding-are-in-pattern-and-have-same-value :
        ∀ (v : A) → (v∈binding : v ∈ binding) → ∃ λ (v∈pfPAT⋐PAT⋒EXP : v ⊰ PAT⋐⋒EXP) → get∈ v∈binding ≡ get⊰ v∈pfPAT⋐PAT⋒EXP

  match? : ∀
    {PAT EXP : Free List A}
    {PAT⋒EXP : PAT ⋒ EXP}
    (PAT⋐PAT⋒EXP : PAT ⋐ PAT⋒EXP)
    (isVar : A → Bool)
    → Dec (Match PAT⋐PAT⋒EXP isVar)
  match? = {!!}

  record SubstitutionAlt
           {s/map}
           {map : M s/map}
           {k : A}
           {l : Free List A}
           {s : Free List A}
           {l⋒s : l ⋒ s}
           (l⋐r : l ⋐ l⋒s)
           (k∈map : k ∈ map)
         : Set₁
         where
    field
      k⊰l⋐r : k ⊰ l⋐r
      alt4 : get⊰ k⊰l⋐r ≡ get∈ k∈map

  record SubstitutionLaw
           {s}
           (binding : M s)
           (PAT : Free List A)
           (isVar : A → Bool)
           (substitutions : Free List A)
           (cappers : PAT ⋒ substitutions)
         : Set₁
         where
    field
      diff2 : PAT ⋐ cappers
      mat : Match diff2 isVar
      law : Match.binding mat ⊆ binding
      law2 : ∀ {a} (a∈binding : a ∈ binding) → a ∉ Match.binding mat → ¬ SubstitutionAlt diff2 a∈binding

  record Substitution
           {s}
           (binding : M s)
           (PAT : Free List A)
           (isVar : A → Bool)
         : Set₁
         where
    field
      substitutions : Free List A
      lem : (cappers : PAT ⋒ substitutions) → SubstitutionLaw binding PAT isVar substitutions cappers

  substitute : ∀ {s} → (binding : M s) → (PAT : Free List A) → (isVar : A → Bool) → Substitution binding PAT isVar
  substitute = {!!}
