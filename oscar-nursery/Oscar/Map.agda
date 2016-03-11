module Oscar.Map where

open import Oscar.Prelude
open import Tactic.Reflection.Reright

module _ {𝑲 𝑽} (let 𝑲𝑽 = 𝑲 ⊔ₗ 𝑽 ; 𝑲𝑽₁ = 𝟙+ₗ 𝑲𝑽) where
  record Map {K : Set 𝑲}
             (V : K → Set 𝑽)
             (Carrier : ℕ → Set 𝑲𝑽) ⦃ isDecEquivalence/K : IsDecEquivalence {A = K} _≡_ ⦄ ⦃ isDecEquivalence/V : (k : K) → IsDecEquivalence {A = V k} _≡_ ⦄
             : Set 𝑲𝑽₁ where
    open IsDecEquivalence isDecEquivalence/K using () renaming (_≟_ to _≟ₖ_)
    open DecTotalOrder decTotalOrder using (_≤?_ ; _≤_ ; total)
--    open IsDecEquivalence isDecEquivalence/V using () renaming (_≟_ to _≟ᵥ_)

    field
      ∅ : Carrier 0
      _∉_ : ∀ {s} → K → Carrier s → Set 𝑲𝑽
      ∅-is-empty : ∀ {𝑘} {∅ : Carrier 0} → 𝑘 ∉ ∅
 
    _∈_ : ∀ {s} → K → Carrier s → Set 𝑲𝑽
    _∈_ k m = ¬ k ∉ m
 
    field
      v⟨_⟩ : ∀ {k : K} {s} {m : Carrier s} → k ∈ m → V k
      get-is-unique : ∀ {k : K} {s} {m : Carrier s} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → v⟨ k∈m¹ ⟩ ≡ v⟨ k∈m² ⟩

    infixl 40 _⊆_
    _⊆_ : ∀ {s₁ s₀} → Carrier s₁ → Carrier s₀ → Set 𝑲𝑽
    _⊆_ m₁ m₀ = ∀ {𝑘} → (𝑘∈m₁ : 𝑘 ∈ m₁) → Σ (𝑘 ∈ m₀) λ 𝑘∈m₀ → v⟨ 𝑘∈m₁ ⟩ ≡ v⟨ 𝑘∈m₀ ⟩

    infixl 40 _⊂_∣_
    _⊂_∣_ : ∀ {s₀ s₁} → Carrier s₀ → Carrier s₁ → (K → Set 𝑲) → Set 𝑲𝑽
    _⊂_∣_ m₀ m₁ c = ∀ {𝑘} → c 𝑘 → (𝑘∈m₀ : 𝑘 ∈ m₀) → Σ (𝑘 ∈ m₁) λ 𝑘∈m₁ → v⟨ 𝑘∈m₀ ⟩ ≡ v⟨ 𝑘∈m₁ ⟩
 
    field
      put' : ∀ {k₀ : K} (v₀ : V k₀) {s₁} {m₁ : Carrier s₁} → k₀ ∉ m₁ → Σ (Carrier (𝟙+ s₁)) λ m₀ → Σ (k₀ ∈ m₀) λ k₀∈m₀ → v⟨ k₀∈m₀ ⟩ ≡ v₀ × m₁ ⊆ m₀ × m₀ ⊂ m₁ ∣ λ 𝑘 → (¬ (𝑘 ≡ k₀))
      _∉?_ : ∀ {s} → (k : K) (m : Carrier s) → Dec (k ∉ m)

    _∈?_ : ∀ {s} → (k : K) (m : Carrier s) → Dec (k ∈ m)
    _∈?_ k m = case k ∉? m of λ
      { (no k∈m) → yes k∈m
      ; (yes k∉m) → no (_$ k∉m)
      }

    field
      choose : ∀ {s₁} → (m₀ : Carrier (𝟙+ s₁)) → ∃ λ k₀ → k₀ ∈ m₀
      pick' : ∀ {k₀ : K} {s₁} {m₀ : Carrier (𝟙+ s₁)} → k₀ ∈ m₀ → ∃ λ (m₁ : Carrier s₁) → m₁ ⊆ m₀ × (m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀) × k₀ ∉ m₁
 
    record Put {k₀ : K} (v₀ : V k₀) {s₁} (m₁ : Carrier s₁) : Set 𝑲𝑽 where
      constructor Put⟦_,_,_,_,_⟧
      field
        m₀ : Carrier (𝟙+ s₁)
        k₀∈m₀ : k₀ ∈ m₀
        v⟨k₀∈m₀⟩≡v₀ : v⟨ k₀∈m₀ ⟩ ≡ v₀
        m₁⊆m₀ : m₁ ⊆ m₀
        m₀⊂m₁∣≢k₀ : m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀
 
    record Pick {k₀ : K} {s₁} {m₀ : Carrier (𝟙+ s₁)} (k₀∈m₀ : k₀ ∈ m₀) : Set 𝑲𝑽 where
      constructor Pick⟦_,_,_,_⟧
      field
        m₁ : Carrier s₁
        m₁⊆m₀ : m₁ ⊆ m₀
        m₀⊂m₁∣≢k₀ : (m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀)
        k₀∉m₁ : k₀ ∉ m₁
 
    put : ∀ {k₀ : K} (v₀ : V k₀) {s₁} {m₁ : Carrier s₁} → k₀ ∉ m₁ → Put v₀ m₁
    put v₀ k₀∉m₁ =
      let
        m₀ , k₀∈m₀ , v⟨k₀∈m₀⟩≡v₀ , m₁⊆m₀ , m₀⊂m₁∣≢k₀ = put' v₀ k₀∉m₁
      in
        record
        { m₀ = m₀
        ; k₀∈m₀ = k₀∈m₀
        ; v⟨k₀∈m₀⟩≡v₀ = v⟨k₀∈m₀⟩≡v₀
        ; m₁⊆m₀ = m₁⊆m₀
        ; m₀⊂m₁∣≢k₀ = m₀⊂m₁∣≢k₀
        }
 
    pick : ∀ {k₀ : K} {s₁} {m₀ : Carrier (𝟙+ s₁)} → (k₀∈m₀ : k₀ ∈ m₀) → Pick k₀∈m₀
    pick k₀∈m₀ = let m₁ , m₁⊆m₀ , m₀⊂m₁∣≢k₀ , k₀∉m₁ = pick' k₀∈m₀ in record
      { m₁ = m₁
      ; m₁⊆m₀ = m₁⊆m₀
      ; m₀⊂m₁∣≢k₀ = m₀⊂m₁∣≢k₀
      ; k₀∉m₁ = k₀∉m₁
      }

    record Union {s/x s/y} (x : Carrier s/x) (y : Carrier s/y) : Set 𝑲𝑽 where
      constructor Union⟦_,_,_,_,_⟧
      field
        s/z : ℕ
        z : Carrier s/z
        x⊆z : x ⊆ z
        y⊆z : y ⊆ z
        z⊆x∪y : ∀ {𝑘} → 𝑘 ∈ z → (𝑘 ∈ x) ⊎ (𝑘 ∈ y)

    abstract
      ∅⊆⋆ : ∀ {x : Carrier 0} {s/y} {y : Carrier s/y} → x ⊆ y
      ∅⊆⋆ {x} {y} 𝑘∈x = contradiction (∅-is-empty {∅ = x}) 𝑘∈x

      ⋆⊆⋆ : ∀ {s/x} {x : Carrier s/x} → x ⊆ x
      ⋆⊆⋆ 𝑘∈x = 𝑘∈x , refl

    infixl 10 _≫=_
    _≫=_ : ∀ {s/x}
              {s/y}
              {s/z}
              {x : Carrier s/x}
              {y : Carrier s/y}
              {z : Carrier s/z}
              {𝑘}
              {𝑘∈x : 𝑘 ∈ x}
              (Σ𝑘∈y : ∃ λ 𝑘∈y → v⟨ 𝑘∈x ⟩ ≡ v⟨ 𝑘∈y ⟩)
              (𝑘∈y→Σ𝑘∈z : (𝑘∈y : 𝑘 ∈ y) → ∃ λ 𝑘∈z → v⟨ 𝑘∈y ⟩ ≡ v⟨ 𝑘∈z ⟩)
            → Σ (𝑘 ∈ z) (λ 𝑘∈z → v⟨ 𝑘∈x ⟩ ≡ v⟨ 𝑘∈z ⟩)
    (𝑘∈y , v⟨𝑘∈x⟩≡v⟨𝑘∈y⟩) ≫= 𝑘∈y→Σ𝑘∈z = ↙ (𝑘∈y→Σ𝑘∈z 𝑘∈y) , trans v⟨𝑘∈x⟩≡v⟨𝑘∈y⟩ (↘ (𝑘∈y→Σ𝑘∈z 𝑘∈y))

    open import Tactic.Nat

    union≤ : ∀ {s/x s/y} (s/x≤s/y : s/x ≤ s/y) (x : Carrier s/x) → (y : Carrier s/y) → Dec (Union x y)
    union≤ {0} {s/y} _ x y  = yes record
      { s/z = s/y
      ; z = y
      ; x⊆z = ∅⊆⋆
      ; y⊆z = ⋆⊆⋆
      ; z⊆x∪y = ↗
      }
    union≤ {𝟙+ s/x₋ₐ} {s/y} s/x≤s/y x y =
      case choose x of λ { (a , a∈x) →
        case pick a∈x of λ { Pick⟦ x₋ₐ , x₋ₐ⊆x , x⊂x₋ₐ|𝑘≢a , a∉x₋ₐ ⟧ →
          case a ∉? y of λ
          { (yes a∉y) →
            case put v⟨ a∈x ⟩ a∉y of λ { Put⟦ y₊ₐ , a∈y₊ₐ , v⟨a∈y₊ₐ⟩≡v⟨a∈x⟩ , y⊆y₊ₐ , y₊ₐ⊂y∣𝑘≢a ⟧ →
              case union≤ (by s/x≤s/y) x₋ₐ y₊ₐ of λ
              -- s/x≤s/y   : 𝟙+ s/x₋ₐ ≤ s/y
              { (yes Union⟦ s/z , z , x₋ₐ⊆z , y₊ₐ⊆z , z⊆x₋ₐ∪y₊ₐ ⟧) →
                yes
                  Union⟦ _ ,
                         z ,
                         (λ {𝑘} 𝑘∈x →
                           (case 𝑘 ≟ₖ a of (λ
                             { (yes 𝑘≡a) → {!reright 𝑘≡a ∘ ↙ $ y₊ₐ⊆z a∈y₊ₐ , ?!}
                             ; (no 𝑘≢a) → x⊂x₋ₐ|𝑘≢a 𝑘≢a 𝑘∈x ≫= x₋ₐ⊆z
                             }))
                         ) ,
                         {!!} ,
                         {!!}
                  ⟧
              ; (no ¬Union⟦x₋ₐ,y₊ₐ⟧) → flip contradiction ¬Union⟦x₋ₐ,y₊ₐ⟧ {!!}
              }
            }
          ; (no a∈y) → {!!}
          }
        }
      }
    
    union : ∀ {s/x s/y} (x : Carrier s/x) → (y : Carrier s/y) → Dec (Union x y)
    union {s/x} {s/y} x y with s/x ≤? s/y
    union {s/x} {s/y} x y | yes s/x≤s/y = union≤ s/x≤s/y x y
    union {s/x} {s/y} x y | no s/x≰s/y with union≤ ([ ⊥-elim ∘ s/x≰s/y , id ]′ $ total s/x s/y) y x
    union {s/x} {s/y} x y | no s/x≰s/y | union< = {!!}
