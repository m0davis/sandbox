module Reduction where
  open import Postlude
  open import Free

  postulate
    A : Set

  V : A → Set₁
  V = λ _ → Free List A

  postulate
    M : ℕ → Set₁
    isDecEquivalence/A : Eq A
    isDecEquivalence/V : (a : A) → Eq (V a)

  open import Map
  postulate
    m : Map V M {{isDecEquivalence/A}} {{isDecEquivalence/V}}

  open FreeComparison {{isDecEquivalence/A}}
  open Map.Map m

  _⋐⋒<Map_ : ∀ {PAT EXP : Free List A} {PAT⋒EXP : PAT ⋒ EXP} (PAT⋐PAT⋒EXP : PAT ⋐ PAT⋒EXP) {s} (binding : M s) → Set₁
  PAT⋐PAT⋒EXP ⋐⋒<Map binding = ∀ {a} (a∈pfPAT⋐PAT⋒EXP : a ∈pf PAT⋐PAT⋒EXP) → ∃ λ (a∈binding : a ∈ binding) → getpf a∈pfPAT⋐PAT⋒EXP ≡ get a∈binding

  _Map<⋐⋒_ : ∀ {s} (binding : M s) {PAT EXP : Free List A} {PAT⋒EXP : PAT ⋒ EXP} (PAT⋐PAT⋒EXP : PAT ⋐ PAT⋒EXP) → Set₁
  binding Map<⋐⋒ PAT⋐PAT⋒EXP = ∀ {a} (a∈binding : a ∈ binding) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PAT⋐PAT⋒EXP) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP

  open import Tactic.Reflection.Reright

  reduce-PureFree-to-map : ∀
    {PAT EXP : Free List A}
    {PAT⋒EXP : PAT ⋒ EXP}
    (PAT⋐PAT⋒EXP : PAT ⋐ PAT⋒EXP)
    → Dec $ ∃ λ s → ∃ λ (binding : M s) → PAT⋐PAT⋒EXP ⋐⋒<Map binding × binding Map<⋐⋒ PAT⋐PAT⋒EXP
  reduce-PureFree-to-map (Equal X≞Y) = yes (0 , ∅ , (λ ()) , (λ {a∈∅ → contradiction ∅-is-empty a∈∅}))
  reduce-PureFree-to-map (PureFree x {N = N} g ns) =
    yes $
      1 ,
      (proj₁ $ put {k₀ = x} (free g ns) {m₁ = ∅} ∅-is-empty) ,
      (λ { {.x} (singleton .x {N = .N} .g .ns) → let s1 , s2 , s3 , s4
                                                         = put {k₀ = x} (free g ns) {m₁ = ∅} ∅-is-empty
                                                   in s2 , (sym $ s3) }) ,
      (λ { {a} a∈binding → case _≟_ {{isDecEquivalence/A}} x a of
        (λ
        { (yes x≡a) → reright x≡a $ λ a∈binding' →
               singleton a g ns ,
               let _ , a∈mₐ , get-a∈mₐ≡free-g-ns , _ = put {k₀ = a} (free g ns) {m₁ = ∅} ∅-is-empty in
                 trans (get-is-unique a∈binding' a∈mₐ) get-a∈mₐ≡free-g-ns
        ; (no x≢a) → case pick a∈binding of (λ { (m0 , k∈m0→Σ , k≢a→k∈m1→Σ , a∉m0) → let s1 , s2 , s3 , s4 = put {k₀ = x} (free g ns) {m₁ = ∅} ∅-is-empty in contradiction ∅-is-empty (proj₁ (k≢a→k∈m1→Σ x≢a s2)) }) })
      })
  reduce-PureFree-to-map (Free∷Free∷ notequal PAT⋐PAT⋒EXP PAT⋐PAT⋒EXP₁) with reduce-PureFree-to-map PAT⋐PAT⋒EXP | reduce-PureFree-to-map PAT⋐PAT⋒EXP₁
  reduce-PureFree-to-map (Free∷Free∷ notequal PAT⋐PAT⋒EXP PAT⋐PAT⋒EXP₁) | yes (_ , m1 , _) | yes (_ , m2 , _) with union m1 m2
  reduce-PureFree-to-map (Free∷Free∷ notequal f r) | yes (s1 , m1 , ∈f→Σ[∈m1,get∈f≡get⋆]   , ∈m1→Σ[∈f,get∈m1≡get⋆])
                                                   | yes (s2 , m2 , ∈r→Σ[∈m2,get∈r≡get⋆]   , ∈m2→Σ[∈r,get∈m2≡get⋆])
                                                   | yes (s3 , m3 , ∈m1→Σ[∈m3,get∈m1≡get⋆] , ∈m2→Σ[∈m3,get∈m2≡get⋆] , ∈m3→∈m1⊎∈m2) = yes $
    s3 ,
    m3 ,
    (λ {∈fr → helper→ ∈f→Σ[∈m1,get∈f≡get⋆] ∈r→Σ[∈m2,get∈r≡get⋆] ∈m1→Σ[∈m3,get∈m1≡get⋆] ∈m2→Σ[∈m3,get∈m2≡get⋆] ∈fr}) ,
    (λ { ∈m3 → case ∈m3→∈m1⊎∈m2 ∈m3 of (λ { (inj₁ ∈m1) → let Σ[∈fr,get⋆≡get∈fr] = helper←1 ∈m1→Σ[∈f,get∈m1≡get⋆] ∈m1→Σ[∈m3,get∈m1≡get⋆] ∈m1 in
                                                         let ∈fr , get⋆≡get∈fr = Σ[∈fr,get⋆≡get∈fr] in
                                                           ∈fr ,
                                                           trans (trans (get-is-unique ∈m3 $ proj₁ $ ∈m1→Σ[∈m3,get∈m1≡get⋆] ∈m1) (sym (proj₂ $ ∈m1→Σ[∈m3,get∈m1≡get⋆] ∈m1))) get⋆≡get∈fr
                                         ; (inj₂ ∈m2) → {!helper←2 ∈m2→Σ[∈r,get∈m2≡get⋆] ∈m2→Σ[∈m3,get∈m2≡get⋆] ∈m2!} }) {-helper← ∈m3→∈m1⊎∈m2 ∈m1→Σ[∈f,get∈m1≡get⋆] ∈m2→Σ[∈r,get∈m2≡get⋆] ∈m1→Σ[∈m3,get∈m1≡get⋆] ∈m2→Σ[∈m3,get∈m2≡get⋆] ∈m3-}}) where
    helper→ : ∀
      {a}
      {M N : Set _} →
      {f : M → Free List A} →
      {m : M} {ms : List M} →
      {g : N → Free List A} →
      {n : N} {ns : List N} →
      {notequal : ¬ free f (m ∷ ms) ≞ free g (n ∷ ns)} →
      {first : f m ⋒ g n} →
      {rest : free f ms ⋒ free g ns} →
      {F : f m ⋐ first}
      {R : free f ms ⋐ rest}
      (∈f→Σ[∈m1,get∈f≡get⋆] : ∀ {a} (∈f : a ∈pf F) → Σ (a ∈ m1) (λ ∈m1 → getpf ∈f ≡ get ∈m1))
      (∈r→Σ[∈m2,get∈f≡get⋆] : ∀ {a} (∈r : a ∈pf R) → Σ (a ∈ m2) (λ ∈m2 → getpf ∈r ≡ get ∈m2))
      (∈m1→Σ[∈m3,get∈m1≡get⋆] : ∀ {𝑘 : A} (𝑘∈m₁ : 𝑘 ∉ m1 → ⊥) → Σ (𝑘 ∉ m3 → ⊥) (λ 𝑘∈m₀ → get 𝑘∈m₁ ≡ get 𝑘∈m₀))
      (∈m2→Σ[∈m3,get∈m2≡get⋆] : ∀ {𝑘 : A} (𝑘∈m₁ : 𝑘 ∉ m2 → ⊥) → Σ (𝑘 ∉ m3 → ⊥) (λ 𝑘∈m₀ → get 𝑘∈m₁ ≡ get 𝑘∈m₀))
      → (∈fr : a ∈pf Free∷Free∷ notequal F R) → Σ (a ∈ m3) (λ a∈m3 → getpf ∈fr ≡ get a∈m3)
    helper→ ∈f→Σ[∈m1,get∈f≡get⋆] _ ∈m1→Σ[∈m3,get∈m1≡get⋆] _ (descend1 a ∈fr) = {!∈f→Σ[∈m1,get∈f≡get⋆] ∈fr!}
    helper→ _ ∈r→Σ[∈m2,get∈f≡get⋆] _ ∈m2→Σ[∈m3,get∈m2≡get⋆] (descend2 a ∈fr) = {!!}
{-
    helper← : ∀
      {a}
      {s3}
      {m3 : M s3}
      (∈m3→∈m1⊎∈m2 : ∀ {𝑘 : A} → (𝑘 ∉ m3 → ⊥) → (𝑘 ∉ m1 → ⊥) ⊎ (𝑘 ∉ m2 → ⊥))
      (∈m1→Σ[∈f,get∈m1≡get⋆] : ∀ {a : A} (a∈binding : a ∉ m1 → ⊥) → Σ ((FreeComparison._∈pf_ {{isDecEquivalence/A}} a) f) (λ a∈pfPAT⋐PAT⋒EXP → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP))
      (∈m2→Σ[∈r,get∈m2≡get⋆] : ∀ {a : A} (a∈binding : a ∉ m2 → ⊥) → Σ ((FreeComparison._∈pf_ {{isDecEquivalence/A}} a) r) (λ a∈pfPAT⋐PAT⋒EXP → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP))
      (∈m1→Σ[∈m3,get∈m1≡get⋆] : ∀ {𝑘 : A} (𝑘∈m₁ : 𝑘 ∉ m1 → ⊥) → Σ (𝑘 ∉ m3 → ⊥) (λ 𝑘∈m₀ → get 𝑘∈m₁ ≡ get 𝑘∈m₀))
      (∈m2→Σ[∈m3,get∈m2≡get⋆] : ∀ {𝑘 : A} (𝑘∈m₁ : 𝑘 ∉ m2 → ⊥) → Σ (𝑘 ∉ m3 → ⊥) (λ 𝑘∈m₀ → get 𝑘∈m₁ ≡ get 𝑘∈m₀))
      → (∈m3 : a ∈ m3) → Σ (a ∈pf Free∷Free∷ notequal f r) (λ ∈fr → get ∈m3 ≡ getpf ∈fr)
    helper← ∈m3→∈m1⊎∈m2 _ _ _ _ ∈m3 with ∈m3→∈m1⊎∈m2 ∈m3
    helper← _ ∈m1→Σ[∈f,get∈m1≡get⋆] _ ∈m1→Σ[∈m3,get∈m1≡get⋆] _ _ | inj₁ ∈m1 = {!∈m1→Σ[∈f,get∈m1≡get⋆] ∈m1!} -- -- ∈m1→Σ[∈m3,get∈m1≡get⋆] ∈m1
    helper← _ _ ∈m2→Σ[∈r,get∈m2≡get⋆] _ ∈m2→Σ[∈m3,get∈m2≡get⋆] _ | inj₂ ∈m2 = {!!}
-}
    helper←1 : ∀
      {a}
      {s1}
      {m1 : M s1}
      (∈m1→Σ[∈f,get∈m1≡get⋆] : ∀ {a : A} (a∈binding : a ∉ m1 → ⊥) → Σ ((FreeComparison._∈pf_ {{isDecEquivalence/A}} a) f) (λ a∈pfPAT⋐PAT⋒EXP → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP))
      (∈m1→Σ[∈m3,get∈m1≡get⋆] : ∀ {𝑘 : A} (𝑘∈m₁ : 𝑘 ∉ m1 → ⊥) → Σ (𝑘 ∉ m3 → ⊥) (λ 𝑘∈m₀ → get 𝑘∈m₁ ≡ get 𝑘∈m₀))
      → (∈m1 : a ∈ m1) → Σ (a ∈pf Free∷Free∷ notequal f r) (λ ∈fr → get ∈m1 ≡ getpf ∈fr)
    helper←1 ∈m1→Σ[∈f,get∈m1≡get⋆] ∈m1→Σ[∈m3,get∈m1≡get⋆] ∈m1 = descend1 _ ∈f , (proj₂ $ ∈m1→Σ[∈f,get∈m1≡get⋆] ∈m1) where
      ∈f = proj₁ $ ∈m1→Σ[∈f,get∈m1≡get⋆] ∈m1

    helper←2 : ∀
      {a}
      {s2}
      {m2 : M s2}
      (∈m2→Σ[∈r,get∈m2≡get⋆] : ∀ {a : A} (a∈binding : a ∉ m2 → ⊥) → Σ ((FreeComparison._∈pf_ {{isDecEquivalence/A}} a) r) (λ a∈pfPAT⋐PAT⋒EXP → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP))
      (∈m2→Σ[∈m3,get∈m2≡get⋆] : ∀ {𝑘 : A} (𝑘∈m₁ : 𝑘 ∉ m2 → ⊥) → Σ (𝑘 ∉ m3 → ⊥) (λ 𝑘∈m₀ → get 𝑘∈m₁ ≡ get 𝑘∈m₀))
      → (∈m2 : a ∈ m2) → Σ (a ∈pf Free∷Free∷ notequal f r) (λ ∈fr → get ∈m2 ≡ getpf ∈fr)
    helper←2 ∈m2→Σ[∈r,get∈m1≡get⋆] ∈m2→Σ[∈m3,get∈m2≡get⋆] ∈m2 = {!!}

  reduce-PureFree-to-map (Free∷Free∷ notequal PAT⋐PAT⋒EXP PAT⋐PAT⋒EXP₁) | yes (s1 , m1 , proj₃ , proj₄) | yes (s2 , m2 , proj7 , proj8) | no ¬p = {!!}
  reduce-PureFree-to-map (Free∷Free∷ notequal PAT⋐PAT⋒EXP PAT⋐PAT⋒EXP₁) | yes (proj₁ , proj₂ , proj₃ , proj₄) | no ¬p = {!!}
  reduce-PureFree-to-map (Free∷Free∷ notequal PAT⋐PAT⋒EXP PAT⋐PAT⋒EXP₁) | no ¬p | yes p = {!!}
  reduce-PureFree-to-map (Free∷Free∷ notequal PAT⋐PAT⋒EXP PAT⋐PAT⋒EXP₁) | no ¬p | no ¬p₁ = {!!}

  postulate
    reduce-PureFree-to-map' : ∀
      {PAT EXP : Free List A}
      {PAT⋒EXP : PAT ⋒ EXP}
      (PAT⋐PAT⋒EXP : PAT ⋐ PAT⋒EXP)
      → Dec
        (
          ∃ λ s
          → ∃ λ (binding : M s)
          → (∀ {a} (a∈pfPAT⋐PAT⋒EXP : a ∈pf PAT⋐PAT⋒EXP) → ∃ λ (a∈binding : a ∈ binding) → getpf a∈pfPAT⋐PAT⋒EXP ≡ get a∈binding)
               ×
            (∀ {a} (a∈binding : a ∈ binding) → ∃ λ (a∈pfPAT⋐PAT⋒EXP : a ∈pf PAT⋐PAT⋒EXP) → get a∈binding ≡ getpf a∈pfPAT⋐PAT⋒EXP)
        )

    substitute : ∀ {s} → M s → Free List A → Free List A
    substitute-law : ∀
      {s}
      {binding : M s}
      (PAT : Free List A) →
      (cappers : PAT ⋒ substitute binding PAT)
      → ∃ λ (diff2 : PAT ⋐ cappers) →
          (let rpf2m = reduce-PureFree-to-map diff2)
          → ∃ λ (prf : True rpf2m) →
            (let reduced = proj₁ (proj₂ (toWitness prf))) →
            reduced ⊆ binding
              ×
            ∀
              {a}
              (a∈binding : a ∈ binding) →
              a ∉ reduced →
              ¬ ∃ λ (a∈pfdiff2 : a ∈pf diff2) → getpf a∈pfdiff2 ≡ get a∈binding
