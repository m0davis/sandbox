module MapAsList where
  module Map0 {α} {K : Set α} (V : K → Set α) where
    open import Level
    open import Relation.Binary.Core
    open import Data.Product
    open import Data.Sum
    open import Data.Unit.Base
    open import Function

    record Maybe {α} (A : Set α) : Set α where
      field
        unmaybe : ⊤ ⊎ A
    
    mutual
      record Map : Set α where
        inductive
        field
          unmap : Maybe (∃ λ k₀ → V k₀ × ∃ λ m₁ → k₀ ∉ m₁)
   
      record _∉_ (𝑘 : K) (m₀ : Map) : Set α where
        inductive
        field
          un∉ : m₀ ≡ record { unmap = record { unmaybe = inj₁ tt } } ⊎
                  ∃ λ m₁ → 𝑘 ∉ m₁ ×
                  ∃ λ k₀ → k₀ ≢ 𝑘 ×
                  ∃ λ (k₀∉m₁ : k₀ ∉ m₁) → ∃ λ v₀
                  → m₀ ≡ record { unmap = record { unmaybe = inj₂ (k₀ , v₀ , m₁ , k₀∉m₁) } }

    open import Data.Empty
    open import Relation.Nullary.Negation
    open import Relation.Nullary 

    _∈_ : (𝑘 : K) (m₀ : Map) → Set α
    𝑘 ∈ m₀ = ¬ 𝑘 ∉ m₀

    pattern M⟦_+_⋆_∣_⟧ m₁ k₀ v₀ k₀∉m₁ = record { unmap = record { unmaybe = inj₂ (k₀ , v₀ , m₁ , k₀∉m₁) } }
    pattern M⟦_+_∣_⟧ m₁ v₀ k₀∉m₁ = record { unmap = record { unmaybe = inj₂ (_ , v₀ , m₁ , k₀∉m₁) } }
    pattern M⟦_⋆_∣_⟧ k₀ v₀ k₀∉m₁ = record { unmap = record { unmaybe = inj₂ (k₀ , v₀ , _ , k₀∉m₁) } }
    pattern M⟦_∣_⟧ v₀ k₀∉m₁ = record { unmap = record { unmaybe = inj₂ (_ , v₀ , _ , k₀∉m₁) } }

    pattern ∅ = record { unmap = record { unmaybe = inj₁ tt } }
    pattern ∉∅ = record { un∉ = (inj₁ refl) }
    pattern ¬∉∅ = record { un∉ = (inj₁ ()) }
    pattern ∉⟦_/_⟧ 𝑘∉m₁ k₀≢𝑘  = record { un∉ = inj₂ (_ , 𝑘∉m₁ , _ , k₀≢𝑘 , _ , _ , refl) }

    here : ∀ {k₀ : K} {v₀ : V k₀} {m₁ : Map} {k₀∉m₁ : k₀ ∉ m₁} → k₀ ∈ M⟦ v₀ ∣ k₀∉m₁ ⟧
    here ¬∉∅
    here ∉⟦ _ / k₀≢k₀ ⟧ = ⊥-elim (k₀≢k₀ refl)

    there : ∀ {𝑘 : K} {m₁ : Map} (𝑘∈m₁ : 𝑘 ∈ m₁) → {k₀ : K} → {v₀ : V k₀} → {k₀∉m₁ : k₀ ∉ m₁} → 𝑘 ∈ M⟦ v₀ ∣ k₀∉m₁ ⟧
    there _ ¬∉∅
    there 𝑘∈m₁ ∉⟦ 𝑘∉m₁ / _ ⟧ = contradiction 𝑘∉m₁ 𝑘∈m₁

    infixl 40 _⊆_
    _⊆_ : Map → Map → Set α
    m ⊆ m' = ∀ {𝑘} → 𝑘 ∉ m' → 𝑘 ∉ m

    infixl 40 _⊂_∣_
    _⊂_∣_ : Map → Map → (K → Set α) → Set α
    m ⊂ m' ∣ c = ∀ {𝑘} → c 𝑘 → 𝑘 ∉ m' → 𝑘 ∉ m

    trans⊂ : ∀ {m m' m''} → (m ⊆ m') → (m' ⊆ m'') → m ⊆ m''
    trans⊂ m⊆m' m'⊆m'' = m⊆m' ∘ m'⊆m''

    shrink : ∀ {k₀ v₀ m₁ k₀∉m₁} → M⟦ m₁ + v₀ ∣ k₀∉m₁ ⟧ ⊂ m₁ ∣ λ 𝑘 → k₀ ≢ 𝑘
    shrink k₀≢𝑘 ∉∅ = ∉⟦ ∉∅ / k₀≢𝑘 ⟧
    shrink k₀≢𝑘 ∉⟦ 𝑘∉m₀ / k₁≢𝑘 ⟧ = ∉⟦ shrink k₁≢𝑘 𝑘∉m₀ / k₀≢𝑘 ⟧
    
    somewhere : ∀ {𝑘 k₀ v₀ m₁ k₀∉m₁} → 𝑘 ∈ M⟦ m₁ + v₀ ∣ k₀∉m₁ ⟧ → k₀ ≢ 𝑘 → 𝑘 ∈ m₁
    somewhere 𝑘∈m₀ k₀≢𝑘 𝑘∉m₁ = contradiction (shrink k₀≢𝑘 𝑘∉m₁) 𝑘∈m₀

    grow : ∀ {k₀ v₀ m₁} {k₀∉m₁ : k₀ ∉ m₁} → m₁ ⊆ M⟦ v₀ ∣ k₀∉m₁ ⟧
    grow ¬∉∅
    grow ∉⟦ ∉∅ / _ ⟧ = ∉∅
    grow ∉⟦ ∉⟦ 𝑘∉m₂ / k₁≢𝑘 ⟧ / _ ⟧ = shrink k₁≢𝑘 𝑘∉m₂

    insert : (k₀ : K) (v₀ : V k₀) {m₁ : Map} (k₀∉m₁ : k₀ ∉ m₁) → ∃ λ m₀ → k₀ ∈ m₀ × m₁ ⊆ m₀ × m₀ ⊂ m₁ ∣ λ 𝑘 → k₀ ≢ 𝑘
    insert k₀ v₀ {m₁} k₀∉m₁ = M⟦ m₁ + v₀ ∣ k₀∉m₁ ⟧ , here , grow , shrink

    choose : (m : Map) → Dec (∃ λ k → k ∈ m)
    choose ∅ = no (λ { (k , k∈m) → k∈m ∉∅ })
    choose M⟦ m₁ + k₀ ⋆ v₀ ∣ k₀∉m₁ ⟧ = yes (k₀ , here)

    open import Relation.Binary
    open import Relation.Binary.PropositionalEquality
    module _ {isDecEquivalence : IsDecEquivalence {A = K} _≡_} where
      open IsDecEquivalence isDecEquivalence using (_≟_)

      _∉?_ : (𝑘 : K) (m₀ : Map) → Dec $ 𝑘 ∉ m₀
      _∉?_ 𝑘 ∅ = yes ∉∅
      _∉?_ 𝑘 M⟦ k₀ ⋆ v₀ ∣ k₀∉m₁ ⟧ with k₀ ≟ 𝑘
      _∉?_ 𝑘 M⟦ m₁ + v₀ ∣ k₀∉m₁ ⟧ | yes k₀≡k rewrite k₀≡k = no here
      _∉?_ 𝑘 M⟦ m₁ + v₀ ∣ k₀∉m₁ ⟧ | no k₀≢𝑘 with 𝑘 ∉? m₁
      _∉?_ 𝑘 M⟦ m₁ + v₀ ∣ k₀∉m₁ ⟧ | no k₀≢𝑘 | yes 𝑘∉m₁ = yes ∉⟦ 𝑘∉m₁ / k₀≢𝑘 ⟧
      _∉?_ 𝑘 M⟦ m₁ + v₀ ∣ k₀∉m₁ ⟧ | no k₀≢𝑘 | no 𝑘∈m₁ = no $ contraposition grow 𝑘∈m₁

      _∈?_ : (𝑘 : K) (m₀ : Map) → Dec $ 𝑘 ∈ m₀
      _∈?_ 𝑘 m₀ = ¬? $ 𝑘 ∉? m₀

      get : ∀ {𝑘 : K} {m₀ : Map} (𝑘∈m₀ : 𝑘 ∈ m₀) → V 𝑘
      get {m₀ = ∅} 𝑘∈m₀ = contradiction ∉∅ 𝑘∈m₀
      get {𝑘} {M⟦ m₁ + k₀ ⋆ v₀ ∣ k₀∉m₁ ⟧} 𝑘∈m₀ with k₀ ≟ 𝑘 
      get {𝑘} {M⟦ m₁ + k₀ ⋆ v₀ ∣ k₀∉m₁ ⟧} 𝑘∈m₀ | yes k₀≡𝑘 rewrite k₀≡𝑘 = v₀
      get {𝑘} {M⟦ m₁ + k₀ ⋆ v₀ ∣ k₀∉m₁ ⟧} 𝑘∈m₀ | no k₀≢𝑘 = get $ somewhere 𝑘∈m₀ k₀≢𝑘

      get-is-unique : ∀ {𝑘 : K} {m₀ : Map} → (k∈m¹ : 𝑘 ∈ m₀) (k∈m² : 𝑘 ∈ m₀) → get k∈m¹ ≡ get k∈m²
      get-is-unique {m₀ = ∅} 𝑘∈m₀ = contradiction ∉∅ 𝑘∈m₀
      get-is-unique {𝑘} {M⟦ m₁ + k₀ ⋆ v₀ ∣ k₀∉m₁ ⟧} 𝑘∈m₀¹ 𝑘∈m₀² with k₀ ≟ 𝑘 
      get-is-unique {𝑘} {M⟦ m₁ + k₀ ⋆ v₀ ∣ k₀∉m₁ ⟧} 𝑘∈m₀¹ 𝑘∈m₀² | yes k₀≡𝑘 rewrite k₀≡𝑘 = refl
      get-is-unique {𝑘} {M⟦ m₁ + k₀ ⋆ v₀ ∣ k₀∉m₁ ⟧} 𝑘∈m₀¹ 𝑘∈m₀² | no k₀≢𝑘 = get-is-unique (somewhere 𝑘∈m₀¹ k₀≢𝑘) (somewhere 𝑘∈m₀² k₀≢𝑘)

      get-it-here : ∀ {k₀ v₀ m₁ k₀∉m₁} → get (here {k₀} {v₀} {m₁} {k₀∉m₁}) ≡ v₀
      get-it-here {k₀} with k₀ ≟ k₀
      get-it-here {k₀} | yes refl = refl
      get-it-here {k₀} | no k₀≢k₀ = ⊥-elim (k₀≢k₀ refl)

      antisym : ∀ {α} {A : Set α} {a b : A} → a ≢ b → b ≢ a
      antisym x x₁ rewrite x₁ = x refl

      put : (k₀ : K) → (v₀ : V k₀) (m₁ : Map) → k₀ ∉ m₁ → ∃ λ (m₀ : Map) → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get k₀∈m₀ ≡ v₀ × (∀ 𝑘 → (𝑘 ∈ m₁ → 𝑘 ∈ m₀)) × (∀ 𝑘 → 𝑘 ≢ k₀ → (𝑘 ∈ m₀ → 𝑘 ∈ m₁))
      put k₀ v₀ m₁ k₀∉m₁ = M⟦ m₁ + k₀ ⋆ v₀ ∣ k₀∉m₁ ⟧ , here , get-it-here , (λ 𝑘 → contraposition grow) , (λ 𝑘 x → contraposition (shrink (antisym x)))

  module Map1 {α} {K : Set α} (V : K → Set α) where
    open import Level
    open import Relation.Binary.Core
    open import Data.Product
    open import Data.Sum
    open import Data.Unit.Base

    open import Data.Empty
    open import Relation.Nullary.Negation
    open import Relation.Nullary
    
    record Map : Set (suc α) where
      inductive
      field
        M : Set α
        ∅ : M
        _∉_ : K → M → Set α
        
      _∈_ : K → M → Set α
      _∈_ k m = ¬ k ∉ m

      field
        get : ∀ {k : K} {m : M} → k ∈ m → V k
        get-is-unique : ∀ {k : K} {m : M} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get k∈m¹ ≡ get k∈m²
        put : (k₀ : K) → (v₀ : V k₀) (m₁ : M) → k₀ ∉ m₁ → ∃ λ (m₀ : M) → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get k₀∈m₀ ≡ v₀ × (∀ 𝑘 → (𝑘 ∈ m₁ → 𝑘 ∈ m₀)) × (∀ 𝑘 → 𝑘 ≢ k₀ → (𝑘 ∈ m₀ → 𝑘 ∈ m₁))
        _∈?_ : (k : K) (m : M) → Dec (k ∈ m)
        choose : (m : M) → Dec (∃ λ k → k ∈ m)
