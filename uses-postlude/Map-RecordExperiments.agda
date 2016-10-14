--{-# OPTIONS -v profile:10 #-}
open import Agda.Builtin.Reflection
open import Postlude
module Map-RecordExperiments
  {𝑲} {K : Set 𝑲}     {{isDecEquivalence/K : Eq K}}
  {𝑽} (V : K → Set 𝑽) {{isDecEquivalence/V : (k : K) → Eq (V k)}}
  (let 𝑲𝑽 = 𝑲 ⊔ₗ 𝑽 ; 𝑲𝑽₁ = sucₗ 𝑲𝑽)
  (Carrier : ℕ → Set 𝑲𝑽)
  where

open import Tactic.Reflection.Reright

record Map₀ : Set 𝑲𝑽₁ where
  field
    ∅ : Carrier 0
    _∈_ : ∀ {s} → K → Carrier s → Set 𝑲𝑽

  _∉_ : ∀ {s} → K → Carrier s → Set 𝑲𝑽
  _∉_ k m = ¬ k ∈ m

  field
    ∅-is-empty : ∀ {𝑘} {∅ : Carrier 0} → 𝑘 ∉ ∅
    get : ∀ {k : K} {s} {m : Carrier s} → k ∈ m → V k
    get-is-unique : ∀ {k : K} {s} {m : Carrier s} → (k∈m¹ : k ∈ m) (k∈m² : k ∈ m) → get k∈m¹ ≡ get k∈m²
--
--record _&∈_ {{map₀ : Map₀}} {k : K} {s₁} {m₁ : Carrier s₁} (k∈m₁ : let open Map₀ map₀ in k ∈ m₁) {s₂} (m₂ : Carrier s₂) : Set 𝑲𝑽 where
--  constructor _,_
--  open Map₀ map₀
--  field
--    proj∈ : k ∈ m₂
--    proj≡ : get k∈m₁ ≡ get proj∈

module _ {{map₀ : Map₀}} where
  open Map₀ map₀
  record _&∈_ {k : K} {s₁} {m₁ : Carrier s₁} (k∈m₁ : k ∈ m₁) {s₂} (m₂ : Carrier s₂) : Set 𝑲𝑽 where
    constructor _,_
    field
      proj∈ : k ∈ m₂
      proj≡ : get k∈m₁ ≡ get proj∈

module _ {{map₀ : Map₀}} where
  open Map₀ map₀
  record _←∋_&∈→_ {s₁} (m₁ : Carrier s₁) (𝑘 : K) {s₂} (m₂ : Carrier s₂) : Set 𝑲𝑽 where
    field
      eq∈ : (𝑘∈m₁ : 𝑘 ∈ m₁) → 𝑘∈m₁ &∈ m₂

record Map : Set 𝑲𝑽₁ where
  field
    isMap₀ : Map₀

  instance
    ism : Map₀
    ism = isMap₀

  open Map₀ isMap₀ public
  open _&∈_
  open _←∋_&∈→_


  infixl 40 _⊆_
  _⊆_ : ∀ {s₀ s₁} → Carrier s₀ → Carrier s₁ → Set 𝑲𝑽
  _⊆_ m₀ m₁ = ∀ {𝑘} → m₀ ←∋ 𝑘 &∈→ m₁


  infixl 40 _⊂_∣_
  _⊂_∣_ : ∀ {s₀ s₁} → Carrier s₀ → Carrier s₁ → (K → Set 𝑲) → Set 𝑲𝑽
  _⊂_∣_ m₀ m₁ c = ∀ {𝑘} → c 𝑘 → m₀ ←∋ 𝑘 &∈→ m₁

  field
    put : ∀ {k₁ : K} (v₁ : V k₁) {s₀} {m₀ : Carrier s₀} → k₁ ∉ m₀ → ∃ λ (m₁ : Carrier (suc s₀)) → (∃ λ (k₁∈m₁ : k₁ ∈ m₁) → get k₁∈m₁ ≡ v₁) × m₀ ⊆ m₁ × m₁ ⊂ m₀ ∣ (_≢ k₁)
    _∈?_ : ∀ {s} → (k : K) (m : Carrier s) → Dec (k ∈ m)
    choose : ∀ {s} → (m : Carrier s) → Dec (∃ λ k → k ∈ m)
    pick : ∀ {k₁ : K} {s₀} {m₁ : Carrier (suc s₀)} → k₁ ∈ m₁ → ∃ λ (m₀ : Carrier s₀) → m₀ ⊆ m₁ × (m₁ ⊂ m₀ ∣ (_≢ k₁)) × k₁ ∉ m₀

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
                (Σa∈z[get/a∈x≡get/a∈z] : a∈x &∈ z) -- Σ (a ∈ z) (λ a∈z → get a∈x ≡ get a∈z))
              → -- Σ (𝑘 ∈ z) (λ 𝑘∈z → get 𝑘∈y ≡ get 𝑘∈z)
                𝑘∈y &∈ z
    helper2 refl get/a∈y≡get/a∈x (a∈z , get/a∈x≡get/z) =
      a∈z ,
      (get-is-unique _ _ ⟨≡⟩ get/a∈y≡get/a∈x ⟨≡⟩ get/a∈x≡get/z)

    infixl 10 _≫=_
    _≫=_ : ∀ {𝑘}
              {s/x} {x : Carrier s/x}
              {𝑘∈x : 𝑘 ∈ x}
              {s/y} {y : Carrier s/y}
              (_ : 𝑘∈x &∈ y)
              {s/z} {z : Carrier s/z}
              --(_ : (𝑘∈y : 𝑘 ∈ y) → 𝑘∈y &∈ z)
              (_ : y ←∋ 𝑘 &∈→ z)
            → 𝑘∈x &∈ z
    (𝑘∈y , xᵏ≡yᵏ) ≫= 𝑘∈y→𝑘∈y&∈z
     with (_←∋_&∈→_.eq∈ 𝑘∈y→𝑘∈y&∈z) 𝑘∈y
    ... | (𝑘∈z , yᵏ≡zᵏ) = 𝑘∈z , (xᵏ≡yᵏ ⟨≡⟩ yᵏ≡zᵏ)

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
  ... | y₊ₐ , (a∈y₊ₐ , y₊ₐᵃ=xᵃ) , y⊆y₊ₐ , y₊ₐ⊂y|≢a
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
                {!!}{-reright 𝑘≡a λ _ →
                  a∈z , (get-is-unique _ _ ⟨≡⟩ y₊ₐᵃ=xᵃ ʳ⟨≡⟩ y₊ₐᵃ=zᵃ)-} }
        ; (no 𝑘≢a) → x⊂x₋ₐ|≢a 𝑘≢a 𝑘∈x ≫= x₋ₐ⊆z })
    , (λ {∈y → y⊆y₊ₐ ∈y ≫= y₊ₐ⊆z})
    , (λ {𝑘} 𝑘∈z →
        case 𝑘 ≟ a of λ
        { (yes 𝑘≡a) → inj₁ (subst _ (sym 𝑘≡a) a∈x)
        ; (no 𝑘≢a) →
            case z⊆x₋ₐ∪y₊ₐ 𝑘∈z of λ
            { (inj₁ 𝑘∈x₋ₐ) → inj₁ $ proj∈ (x₋ₐ⊆x 𝑘∈x₋ₐ)
            ; (inj₂ 𝑘∈y₊ₐ) → inj₂ $ proj∈ (y₊ₐ⊂y|≢a 𝑘≢a 𝑘∈y₊ₐ) } })
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
                { (inj₁ ∈x) → inj₁ $ proj∈ (x⊂x₋ₐ|≢a k≢a ∈x)
                ; (inj₂ ∈y) → inj₂ $ proj∈ (y⊆y₊ₐ ∈y) } }) }
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
                  {!!}{-reright 𝑘≡a λ _ →
                    a∈z , (get-is-unique _ _ ⟨≡⟩ vxₐ≡vyₐ ⟨≡⟩ vyₐ≡vzₐ)-} }
          ; (no 𝑘≢a) → x⊂x₋ₐ|≢a 𝑘≢a 𝑘∈x ≫= x₋ₐ⊆z
          })
        ) ,
        (λ {∈y → y⊆z ∈y}) ,
        (λ {∈z → case z⊆x₋ₐ∪y ∈z of
          (λ {
            (inj₁ ∈x₋ₐ) → inj₁ $ proj∈ (x₋ₐ⊆x ∈x₋ₐ)
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
                    (no 𝑘≢a) → inj₁ $ proj∈ $ x⊂x₋ₐ|≢a 𝑘≢a ∈x
                  })
              ; (inj₂ ∈y) → inj₂ ∈y
              })
            )
          )
          ¬unionx₋ₐy })
    })
  ... | no vx≢vy = no (λ { (s/z , z , x⊆z , y⊆z , z⊆x∪y) →
    let get/a∈zX≡get/a∈zY = get-is-unique (proj∈ (x⊆z a∈x)) (proj∈ (y⊆z a∈y))
        get/a∈x≡get/a∈zX = proj≡ (x⊆z a∈x)
        get/a∈x≡get/a∈zY = proj≡ (y⊆z a∈y)
    in contradiction (get/a∈x≡get/a∈zX ⟨≡⟩ get/a∈zX≡get/a∈zY ⟨≡⟩ʳ get/a∈x≡get/a∈zY) vx≢vy
    })
  union {suc s/x₋ₐ} x y | no ∉x = yes $
    _ ,
    y ,
    (λ {𝑘} ∈x → contradiction (𝑘 , ∈x) ∉x) ,
    (λ {∈y → ∈y , refl}) ,
    (λ {∈y → inj₂ ∈y})
