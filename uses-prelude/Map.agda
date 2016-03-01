module Map where
  open import Prelude
  
  module _ {𝑲 𝑽} (let 𝑲𝑽 = 𝑲 ⊔ 𝑽 ; 𝑲𝑽₁ = lsuc 𝑲𝑽) where
    record Map {K : Set 𝑲}
               (V : K → Set 𝑽)
               (Carrier : Nat → Set 𝑲𝑽) {{isDecEquivalence/K : Eq K}} {{isDecEquivalence/V : (k : K) → Eq (V k)}}
               : Set 𝑲𝑽₁ where
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
        put' : ∀ {k₀ : K} (v₀ : V k₀) {s₁} {m₁ : Carrier s₁} → k₀ ∉ m₁ → Σ (Carrier (suc s₁)) λ m₀ → Σ (k₀ ∈ m₀) λ k₀∈m₀ → v⟨ k₀∈m₀ ⟩ ≡ v₀ × m₁ ⊆ m₀ × m₀ ⊂ m₁ ∣ λ 𝑘 → (¬ (𝑘 ≡ k₀))
        _∉?_ : ∀ {s} → (k : K) (m : Carrier s) → Dec (k ∉ m)

      _∈?_ : ∀ {s} → (k : K) (m : Carrier s) → Dec (k ∈ m)
      _∈?_ k m = case k ∉? m of λ
        { (no k∈m) → yes k∈m
        ; (yes k∉m) → no (_$ k∉m)
        }

      field
        choose : ∀ {s₁} → (m₀ : Carrier (suc s₁)) → ∃ λ k₀ → k₀ ∈ m₀
        pick' : ∀ {k₀ : K} {s₁} {m₀ : Carrier (suc s₁)} → k₀ ∈ m₀ → ∃ λ (m₁ : Carrier s₁) → m₁ ⊆ m₀ × (m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀) × k₀ ∉ m₁
   
      record Put {k₀ : K} (v₀ : V k₀) {s₁} (m₁ : Carrier s₁) : Set 𝑲𝑽 where
        constructor Put⟦_,_,_,_,_⟧
        field
          m₀ : Carrier (suc s₁)
          k₀∈m₀ : k₀ ∈ m₀
          v⟨k₀∈m₀⟩≡v₀ : v⟨ k₀∈m₀ ⟩ ≡ v₀
          m₁⊆m₀ : m₁ ⊆ m₀
          m₀⊂m₁∣≢k₀ : m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀
   
      record Pick {k₀ : K} {s₁} {m₀ : Carrier (suc s₁)} (k₀∈m₀ : k₀ ∈ m₀) : Set 𝑲𝑽 where
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
   
      pick : ∀ {k₀ : K} {s₁} {m₀ : Carrier (suc s₁)} → (k₀∈m₀ : k₀ ∈ m₀) → Pick k₀∈m₀
      pick k₀∈m₀ = let m₁ , m₁⊆m₀ , m₀⊂m₁∣≢k₀ , k₀∉m₁ = pick' k₀∈m₀ in record
        { m₁ = m₁
        ; m₁⊆m₀ = m₁⊆m₀
        ; m₀⊂m₁∣≢k₀ = m₀⊂m₁∣≢k₀
        ; k₀∉m₁ = k₀∉m₁
        }

      record Union {s/x s/y} (x : Carrier s/x) (y : Carrier s/y) : Set 𝑲𝑽 where
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
      
      union : ∀ {s/x s/y} (x : Carrier s/x) → (y : Carrier s/y) → Dec (Union x y)
      union {0} {s/y} x y  = yes record
        { s/z = s/y
        ; z = y
        ; x⊆z = ∅⊆⋆
        ; y⊆z = ⋆⊆⋆
        ; z⊆x∪y = inj₂
        }
      union {suc s/x} x y =
        let a , a∈x = choose x
            Pick⟦ x₋ₐ , x₋ₐ⊆x , x⊂x₋ₐ|≢a , a∉x₋ₐ ⟧ = pick a∈x
        in 
          case a ∈? y of λ
          { (yes a∈y) → {!!}
          ; (no a∉y) → {!!}
          }
      
  postulate
    K : Set
    V : K → Set
    M : ℕ → Set
    isDecEquivalence/K : Eq K
    isDecEquivalence/V : (k : K) → Eq (V k)
    m : Map V M {{isDecEquivalence/K}} {{isDecEquivalence/V}}

  open Map m
  
  foo : ∅ ≡ ∅
  foo = {!put!}
  
