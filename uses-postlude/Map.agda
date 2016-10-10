--{-# OPTIONS -v profile:10 #-}
open import Agda.Builtin.Reflection
module Map where
  open import Postlude
  open import Tactic.Reflection.Reright

  module _ {𝑲 𝑽} (let 𝑲𝑽 = 𝑲 ⊔ₗ 𝑽 ; 𝑲𝑽₁ = sucₗ 𝑲𝑽) where
    record Map
             {K : Set 𝑲}
             (V : K → Set 𝑽)
             (Carrier : ℕ → Set 𝑲𝑽) {{isDecEquivalence/K : Eq K}} {{isDecEquivalence/V : (k : K) → Eq (V k)}} : Set 𝑲𝑽₁ where
      field
        ∅ : Carrier 0
        _∈_ : ∀ {s} → K → Carrier s → Set 𝑲𝑽

      _∉_ : ∀ {s} → K → Carrier s → Set 𝑲𝑽
      _∉_ k m = ¬ k ∈ m

      field
        ∅-is-empty : ∀ {𝑘} {∅ : Carrier 0} → 𝑘 ∉ ∅
        get : ∀ {k : K} {s} {m : Carrier s} → k ∈ m → V k
        get-is-unique : ∀ {k : K} {s} {m : Carrier s} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get k∈m¹ ≡ get k∈m²

      infixl 40 _⊆_
      _⊆_ : ∀ {s₁ s₀} → Carrier s₁ → Carrier s₀ → Set 𝑲𝑽
      _⊆_ m₁ m₀ = ∀ {𝑘} → (𝑘∈m₁ : 𝑘 ∈ m₁) → ∃ λ (𝑘∈m₀ : 𝑘 ∈ m₀) → get 𝑘∈m₁ ≡ get 𝑘∈m₀

      infixl 40 _⊂_∣_
      _⊂_∣_ : ∀ {s₀ s₁} → Carrier s₀ → Carrier s₁ → (K → Set 𝑲) → Set 𝑲𝑽
      _⊂_∣_ m₀ m₁ c = ∀ {𝑘} → c 𝑘 → (𝑘∈m₀ : 𝑘 ∈ m₀) → ∃ λ (𝑘∈m₁ : 𝑘 ∈ m₁) → get 𝑘∈m₀ ≡ get 𝑘∈m₁

      field
        put : ∀ {k₀ : K} (v₀ : V k₀) {s₁} {m₁ : Carrier s₁} → k₀ ∉ m₁ → ∃ λ (m₀ : Carrier (suc s₁)) → ∃ λ (k₀∈m₀ : k₀ ∈ m₀) → get k₀∈m₀ ≡ v₀ × m₁ ⊆ m₀ × m₀ ⊂ m₁ ∣ (_≢ k₀)
        _∈?_ : ∀ {s} → (k : K) (m : Carrier s) → Dec (k ∈ m)
        choose : ∀ {s} → (m : Carrier s) → Dec (∃ λ k → k ∈ m)
        pick : ∀ {k₀ : K} {s₁} {m₀ : Carrier (suc s₁)} → k₀ ∈ m₀ → ∃ λ (m₁ : Carrier s₁) → m₁ ⊆ m₀ × (m₀ ⊂ m₁ ∣ λ 𝑘 → 𝑘 ≢ k₀) × k₀ ∉ m₁

      private
        helper2 : ∀ {𝑘}
                    {a}
                    {s/x}
                    {s/y}
                    {s/z}
                    {x : Carrier s/x}
                    {y : Carrier s/y}
                    {z : Carrier s/z}
                    {a∈x : a ∈ x}
                    {a∈y : a ∈ y}
                    (𝑘≡a : 𝑘 ≡ a)
                    {𝑘∈y : 𝑘 ∈ y}
                    (get/a∈y≡get/a∈x : get a∈y ≡ get a∈x)
                    (Σa∈z[get/a∈x≡get/a∈z] : Σ (a ∈ z) (λ a∈z → get a∈x ≡ get a∈z))
                  → Σ (𝑘 ∈ z) (λ 𝑘∈z → get 𝑘∈y ≡ get 𝑘∈z)
        helper2 refl get/a∈y≡get/a∈x (a∈z , get/a∈x≡get/z) =
          a∈z ,
          trans (get-is-unique _ _) (trans get/a∈y≡get/a∈x get/a∈x≡get/z)

        infixl 10 _≫=_
        _≫=_ : ∀ {𝑘}
                  {s/x}
                  {s/y}
                  {s/z}
                  {x : Carrier s/x}
                  {y : Carrier s/y}
                  {z : Carrier s/z}
                  {𝑘∈x : 𝑘 ∈ x}
                  (Σ𝑘∈y : Σ (𝑘 ∈ y) (λ 𝑘∈y → get 𝑘∈x ≡ get 𝑘∈y))
                  (𝑘∈y→Σ𝑘∈z : (𝑘∈y : 𝑘 ∈ y) → Σ (𝑘 ∈ z) (λ 𝑘∈z → get 𝑘∈y ≡ get 𝑘∈z))
                → Σ (𝑘 ∈ z) (λ 𝑘∈z → get 𝑘∈x ≡ get 𝑘∈z)
        (𝑘∈y , vxₖ≡vyₖ) ≫= 𝑘∈y→Σ𝑘∈z = proj₁ (𝑘∈y→Σ𝑘∈z 𝑘∈y) , (vxₖ≡vyₖ ⟨≡⟩ proj₂ (𝑘∈y→Σ𝑘∈z 𝑘∈y))

      record ⟦_∪_⟧ {s/x s/y} (x : Carrier s/x) (y : Carrier s/y) : Set 𝑲𝑽 where
        field
          {s/z} : _
          z : Carrier s/z
          x⊆z : x ⊆ z
          y⊆z : y ⊆ z
          z⊆x∪y : ∀ {k} → k ∈ z → (k ∈ x) ⊎ (k ∈ y)
{-
      [_∪_] : ∀ {s/x s/y} (x : Carrier s/x) (y : Carrier s/y) → Dec ⟦ x ∪ y ⟧
      [_∪_] {0} x y =
        yes record
          { s/z = _
          ; z = y
          ; x⊆z = {!!}
          ; y⊆z = {!!}
          ; z⊆x∪y = {!!} }
      [_∪_] {_} x y = {!!}
-}
      union : ∀ {s/x s/y} (x : Carrier s/x) (y : Carrier s/y) → Dec (∃ λ s/z → ∃ λ (z : Carrier s/z) → (x ⊆ z) × (y ⊆ z) × ∀ {𝑘} → 𝑘 ∈ z → ((𝑘 ∈ x) ⊎ (𝑘 ∈ y)))
      union {0} x y = yes $
        _ ,
        y ,
        (λ {𝑘∈x → contradiction 𝑘∈x (∅-is-empty {∅ = x})}) ,
        (λ {𝑘∈y → 𝑘∈y , refl}) ,
        (λ {𝑘∈y → inj₂ 𝑘∈y})
      union {suc s/x₋ₐ} x y
       with choose x
      union {suc s/x₋ₐ} x y | yes (a , a∈x)
       with pick a∈x | a ∈? y
      ... | x₋ₐ , x₋ₐ⊆x , x⊂x₋ₐ|≢a , a∉x₋ₐ | no a∉y
       with put (get a∈x) a∉y
      ... | y₊ₐ , a∈y₊ₐ , y₊ₐᵃ=xᵃ , y⊆y₊ₐ , y₊ₐ⊂y|≢a
       with union x₋ₐ y₊ₐ
      ... | yes (s/z , z , x₋ₐ⊆z , y₊ₐ⊆z , z⊆x₋ₐ∪y₊ₐ) =
        yes
        $ _
        , z
        , (λ {𝑘} 𝑘∈x →
            case 𝑘 ≟ a of λ
            { (yes 𝑘≡a) →
                case y₊ₐ⊆z a∈y₊ₐ of λ
                { (a∈z , y₊ₐᵃ=zᵃ) →
                    reright 𝑘≡a λ _ →
                      a∈z , (get-is-unique _ _ ⟨≡⟩ y₊ₐᵃ=xᵃ ʳ⟨≡⟩ y₊ₐᵃ=zᵃ) }
            ; (no 𝑘≢a) → x⊂x₋ₐ|≢a 𝑘≢a 𝑘∈x ≫= x₋ₐ⊆z })
        , (λ {∈y → y⊆y₊ₐ ∈y ≫= y₊ₐ⊆z})
        , (λ {𝑘} 𝑘∈z →
            case 𝑘 ≟ a of λ
            { (yes 𝑘≡a) → inj₁ (subst _ (sym 𝑘≡a) a∈x)
            ; (no 𝑘≢a) →
                case z⊆x₋ₐ∪y₊ₐ 𝑘∈z of λ
                { (inj₁ 𝑘∈x₋ₐ) → inj₁ $ proj₁ (x₋ₐ⊆x 𝑘∈x₋ₐ)
                ; (inj₂ 𝑘∈y₊ₐ) → inj₂ $ proj₁ (y₊ₐ⊂y|≢a 𝑘≢a 𝑘∈y₊ₐ) } })
      ... | no ¬unionx₋ₐy₊ₐ =
        no $
        λ { (s/z , z , x⊆z , y⊆z , z⊆x∪y) →
          flip contradiction
            ¬unionx₋ₐy₊ₐ
            $ s/z
            , z
            , (λ {∈x₋ₐ → x₋ₐ⊆x ∈x₋ₐ ≫= λ ∈x → x⊆z ∈x})
            , (λ {𝑘} ∈y₊ₐ →
                case 𝑘 ≟ a of λ
                { (yes 𝑘≡a) → helper2 𝑘≡a y₊ₐᵃ=xᵃ (x⊆z a∈x)
                ; (no 𝑘≢a) → y₊ₐ⊂y|≢a 𝑘≢a ∈y₊ₐ ≫= λ ∈y → y⊆z ∈y })
            , (λ {𝑘} ∈z →
                case 𝑘 ≟ a of λ
                { (yes k≡a) → inj₂ (subst _ (sym k≡a) a∈y₊ₐ)
                ; (no k≢a) →
                    case z⊆x∪y ∈z of λ
                    { (inj₁ ∈x) → inj₁ $ proj₁ (x⊂x₋ₐ|≢a k≢a ∈x)
                    ; (inj₂ ∈y) → inj₂ $ proj₁ (y⊆y₊ₐ ∈y) } }) }
      union {suc s/x₋ₐ} x y | yes (a , a∈x) | x₋ₐ , x₋ₐ⊆x , x⊂x₋ₐ|≢a , a∉x₋ₐ | yes a∈y with (_≟_ {{isDecEquivalence/V a}} (get a∈x) (get a∈y))
      ... | yes vxₐ≡vyₐ = case union x₋ₐ y of
        (λ {
          (yes (s/z , z , x₋ₐ⊆z , y⊆z , z⊆x₋ₐ∪y)) → yes $
            _ ,
            z ,
            (λ {𝑘} 𝑘∈x → case 𝑘 ≟ a of
              (λ {
                (yes 𝑘≡a) →
                  case y⊆z a∈y of λ
                  { (a∈z , vyₐ≡vzₐ) →
                      reright 𝑘≡a λ _ →
                        a∈z , (get-is-unique _ _ ⟨≡⟩ vxₐ≡vyₐ ⟨≡⟩ vyₐ≡vzₐ) }
              ; (no 𝑘≢a) → x⊂x₋ₐ|≢a 𝑘≢a 𝑘∈x ≫= x₋ₐ⊆z
              })
            ) ,
            (λ {∈y → y⊆z ∈y}) ,
            (λ {∈z → case z⊆x₋ₐ∪y ∈z of
              (λ {
                (inj₁ ∈x₋ₐ) → inj₁ $ proj₁ (x₋ₐ⊆x ∈x₋ₐ)
              ; (inj₂ ∈y) → inj₂ ∈y
              })
            }) ;
          (no ¬unionx₋ₐy) → no (λ { (s/z , z , x⊆z , y⊆z , z⊆x∪y) →
            contradiction
              (
                _ ,
                z ,
                (λ {∈x₋ₐ → x₋ₐ⊆x ∈x₋ₐ ≫= λ 𝑘∈x₋ₐ → x⊆z 𝑘∈x₋ₐ}) ,
                y⊆z ,
                (λ {𝑘} ∈z → case z⊆x∪y ∈z of
                  (λ {
                    (inj₁ ∈x) → case 𝑘 ≟ a of
                      (λ {
                        (yes 𝑘≡a) → inj₂ (subst _ (sym 𝑘≡a) a∈y) ;
                        (no 𝑘≢a) → inj₁ $ proj₁ $ x⊂x₋ₐ|≢a 𝑘≢a ∈x
                      })
                  ; (inj₂ ∈y) → inj₂ ∈y
                  })
                )
              )
              ¬unionx₋ₐy })
        })
      ... | no vx≢vy = no (λ { (s/z , z , x⊆z , y⊆z , z⊆x∪y) →
        let get/a∈zX≡get/a∈zY = get-is-unique (proj₁ (x⊆z a∈x)) (proj₁ (y⊆z a∈y))
            get/a∈x≡get/a∈zX = proj₂ (x⊆z a∈x)
            get/a∈x≡get/a∈zY = proj₂ (y⊆z a∈y)
        in contradiction (get/a∈x≡get/a∈zX ⟨≡⟩ get/a∈zX≡get/a∈zY ⟨≡⟩ʳ get/a∈x≡get/a∈zY) vx≢vy
        })
      union {suc s/x₋ₐ} x y | no ∉x = yes $
        _ ,
        y ,
        (λ {𝑘} ∈x → contradiction (𝑘 , ∈x) ∉x) ,
        (λ {∈y → ∈y , refl}) ,
        (λ {∈y → inj₂ ∈y})
