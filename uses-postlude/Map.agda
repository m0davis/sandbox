--{-# OPTIONS -v profile:10 #-}
open import Agda.Builtin.Reflection
open import Postlude
module Map {𝑲} {K : Set 𝑲}     ⦃ isDecEquivalence/K : Eq K ⦄
           {𝑽} (V : K → Set 𝑽) ⦃ isDecEquivalence/V : {k : K} → Eq (V k) ⦄
           (let 𝑲𝑽 = 𝑲 ⊔ₗ 𝑽 ; 𝑲𝑽₁ = sucₗ 𝑲𝑽)
           (Carrier : ℕ → Set 𝑲𝑽)
       where

open import Tactic.Reright

record Map : Set 𝑲𝑽₁ where
  field
    _∈_ : ∀ {s} → K → Carrier s → Set 𝑲𝑽

  _∉_ : ∀ {s} → K → Carrier s → Set 𝑲𝑽
  _∉_ k m = ¬ k ∈ m

  field
    ∅-is-empty : ∀ {𝑘} {∅ : Carrier 0} → 𝑘 ∉ ∅
    get : ∀ {k : K} {s} {m : Carrier s} → k ∈ m → V k
    get-is-unique : ∀ {k : K} {s} {m : Carrier s} → {k∈m¹ : k ∈ m} {k∈m² : k ∈ m} → get k∈m¹ ≡ get k∈m²

  infixl 40 _⊆_
  _⊆_ : ∀ {s₀ s₁} → Carrier s₀ → Carrier s₁ → Set 𝑲𝑽
  _⊆_ m₀ m₁ = ∀ {𝑘} → (𝑘∈m₀ : 𝑘 ∈ m₀) → ∃ λ 𝑘∈m₁ → get 𝑘∈m₀ ≡ get {m = m₁} 𝑘∈m₁

  infixl 40 _⊂_∣_
  _⊂_∣_ : ∀ {s₀ s₁} → Carrier s₀ → Carrier s₁ → (K → Set 𝑲) → Set 𝑲𝑽
  _⊂_∣_ m₀ m₁ c = ∀ {𝑘} → c 𝑘 → (𝑘∈m₀ : 𝑘 ∈ m₀) → ∃ λ (𝑘∈m₁ : 𝑘 ∈ m₁) → get 𝑘∈m₀ ≡ get 𝑘∈m₁

  field
    put : ∀ {k₁ : K} (v₁ : V k₁) {s₀} {m₀ : Carrier s₀} → k₁ ∉ m₀ → ∃ λ (m₁ : Carrier (suc s₀)) → ∃ λ (k₁∈m₁ : k₁ ∈ m₁) → get k₁∈m₁ ≡ v₁ × m₀ ⊆ m₁ × m₁ ⊂ m₀ ∣ (_≢ k₁)
    _∈?_ : ∀ {s} → (k : K) (m : Carrier s) → Dec (k ∈ m)
    choose : ∀ {s} → (m : Carrier s) → Dec (∃ λ k → k ∈ m)
    pick : ∀ {k₁ : K} {s₀} {m₁ : Carrier (suc s₀)} → k₁ ∈ m₁ → ∃ λ (m₀ : Carrier s₀) → m₀ ⊆ m₁ × (m₁ ⊂ m₀ ∣ (_≢ k₁)) × k₁ ∉ m₀
{-
  private
    infixl 10 _≫=_
    _≫=_ : ∀ {𝑘}
              {s/x}
              {s/y}
              {s/z}
              {x : Carrier s/x}
              {y : Carrier s/y}
              {z : Carrier s/z}
              {𝑘∈x : 𝑘 ∈ x}
              (Σ𝑘∈y : ∃ λ 𝑘∈y → get 𝑘∈x ≡ get 𝑘∈y)
              (𝑘∈y→Σ𝑘∈z : (𝑘∈y : 𝑘 ∈ y) → ∃ λ 𝑘∈z → get 𝑘∈y ≡ get {m = z} 𝑘∈z)
            → ∃ λ 𝑘∈z → get 𝑘∈x ≡ get 𝑘∈z
    (𝑘∈y , xᵏ≡yᵏ) ≫= 𝑘∈y→Σ𝑘∈z
     with 𝑘∈y→Σ𝑘∈z 𝑘∈y
    ... | (𝑘∈z , yᵏ≡zᵏ) = 𝑘∈z , (xᵏ≡yᵏ ⟨≡⟩ yᵏ≡zᵏ)

    _⟨⊆⟩_ : ∀ {s/x}
              {s/y}
              {s/z}
              {x : Carrier s/x}
              {y : Carrier s/y}
              {z : Carrier s/z}
              (x⊆y : x ⊆ y)
              (y⊆z : y ⊆ z)
              → x ⊆ z
    x⊆y ⟨⊆⟩ y⊆z = _≫= y⊆z ∘ x⊆y

  record ⟦_∪_⟧ {s/◭ s/◮} (◭ : Carrier s/◭) (◮ : Carrier s/◮) : Set 𝑲𝑽 where
    constructor ⟪_,_,_⟫
    field
      {s/▲} : ℕ
      {▲} : Carrier s/▲
      ◭⊆▲ : ◭ ⊆ ▲
      ◮⊆▲ : ◮ ⊆ ▲
      ▲⊆◭∪◮ : ∀ {k} → k ∈ ▲ → (k ∈ ◭) ⊎ (k ∈ ◮)

  [_∪_] : ∀ {s/◭ s/◮} (◭ : Carrier s/◭) (◮ : Carrier s/◮) → Dec ⟦ ◭ ∪ ◮ ⟧
  [_∪_] {0} ◭ ◮ =
    yes record
      { ◭⊆▲ = λ {𝑘∈⋆ → contradiction 𝑘∈⋆ ∅-is-empty}
      ; ◮⊆▲ = _, refl
      ; ▲⊆◭∪◮ = inj₂ }
  [_∪_] {suc s/◭₋ₐ} ◭ ◮ =
    case choose ◭ of λ
    { (yes (a , a∈◭)) →
      let (◭₋ₐ , ◭₋ₐ⊆◭ , ◭⊂◭₋ₐ|≢a , a∉◭₋ₐ) = pick a∈◭ in
      case a ∈? ◮ of λ
      { (no a∉◮) →
        let (◮₊ₐ , a∈◮₊ₐ , ◮₊ₐᵃ=◭ᵃ , ◮⊆◮₊ₐ , ◮₊ₐ⊂◮|≢a) = put (get a∈◭) a∉◮ in
        case [ ◭₋ₐ ∪ ◮₊ₐ ] of λ
        { (yes ⟪ ◭₋ₐ⊆▲ , ◮₊ₐ⊆▲ , ▲⊆◭₋ₐ∪◮₊ₐ ⟫) →
          yes
          record
          { ◭⊆▲ =
            λ {𝑘} 𝑘∈◭ →
            case 𝑘 ≟ a of λ
            { (yes 𝑘≡a) →
              reright 𝑘≡a λ _ →
              let (a∈▲ , ◮₊ₐᵃ=▲ᵃ) = ◮₊ₐ⊆▲ a∈◮₊ₐ in
              a∈▲ ,
              (get-is-unique ⟨≡⟩ ◮₊ₐᵃ=◭ᵃ ʳ⟨≡⟩ ◮₊ₐᵃ=▲ᵃ)
            ; (no 𝑘≢a) → ◭⊂◭₋ₐ|≢a 𝑘≢a 𝑘∈◭ ≫= ◭₋ₐ⊆▲ }
          ; ◮⊆▲ = ◮⊆◮₊ₐ ⟨⊆⟩ ◮₊ₐ⊆▲
          ; ▲⊆◭∪◮ =
            λ {𝑘} 𝑘∈▲ →
            case ▲⊆◭₋ₐ∪◮₊ₐ 𝑘∈▲ of λ
            { (inj₁ 𝑘∈◭₋ₐ) → inj₁ ∘′ proj₁ $ ◭₋ₐ⊆◭ 𝑘∈◭₋ₐ
            ; (inj₂ 𝑘∈◮₊ₐ) →
              case 𝑘 ≟ a of λ
              { (yes 𝑘≡a) → inj₁ $ subst _ (sym 𝑘≡a) a∈◭
              ; (no 𝑘≢a) → inj₂ ∘′ proj₁ $ ◮₊ₐ⊂◮|≢a 𝑘≢a 𝑘∈◮₊ₐ } } }
        ; (no ∄◭₋ₐ∪◮₊ₐ) →
          no
          λ { ⟪ ◭⊆▲ , ◮⊆▲ , ▲⊆◭∪◮ ⟫ →
          flip contradiction
          ∄◭₋ₐ∪◮₊ₐ
          record
          { ◭⊆▲ = -- ◭₋ₐ ⊆ ▲
            ◭₋ₐ⊆◭ ⟨⊆⟩ ◭⊆▲
          ; ◮⊆▲ = -- ◮₊ₐ ⊆ ▲
            λ {𝑘} 𝑘∈◮₊ₐ →
            case 𝑘 ≟ a of λ
            { (yes 𝑘≡a) →
              reright 𝑘≡a λ _ →
              let (a∈▲ , ◮ᵃ=▲ᵃ) = ◭⊆▲ a∈◭ in
              a∈▲ ,
              (get-is-unique ⟨≡⟩ ◮₊ₐᵃ=◭ᵃ ⟨≡⟩ ◮ᵃ=▲ᵃ)
            ; (no 𝑘≢a) → ◮₊ₐ⊂◮|≢a 𝑘≢a 𝑘∈◮₊ₐ ≫= ◮⊆▲ }
          ; ▲⊆◭∪◮ = -- ▲ ⊆ ◭₋ₐ ∪ ◮₊ₐ
            λ {𝑘} 𝑘∈▲ →
            case ▲⊆◭∪◮ 𝑘∈▲ of λ
            { (inj₁ 𝑘∈◭) →
              case 𝑘 ≟ a of λ
              { (yes 𝑘≡a) → inj₂ $ subst _ (sym 𝑘≡a) a∈◮₊ₐ
              ; (no 𝑘≢a) → inj₁ ∘′ proj₁ $ ◭⊂◭₋ₐ|≢a 𝑘≢a 𝑘∈◭ }
            ; (inj₂ 𝑘∈◮) → inj₂ ∘′ proj₁ $ ◮⊆◮₊ₐ 𝑘∈◮ } } } }
      ; (yes a∈◮) →
        case get a∈◭ ≟ get a∈◮ of λ
        { (yes ◭ᵃ=◮ᵃ) →
          case [ ◭₋ₐ ∪ ◮ ] of λ
          { (yes ⟪ ◭₋ₐ⊆▲ , ◮⊆▲ , ▲⊆◭₋ₐ∪◮ ⟫) →
            yes
            ⟪ (λ {𝑘} 𝑘∈◭ →
              case 𝑘 ≟ a of λ
              { (yes 𝑘≡a) →
                reright 𝑘≡a λ _ →
                let (a∈▲ , ◮ᵃ=▲ᵃ) = ◮⊆▲ a∈◮ in
                a∈▲ , (get-is-unique ⟨≡⟩ ◭ᵃ=◮ᵃ ⟨≡⟩ ◮ᵃ=▲ᵃ)
              ; (no 𝑘≢a) → ◭⊂◭₋ₐ|≢a 𝑘≢a 𝑘∈◭ ≫= ◭₋ₐ⊆▲ })
            , ◮⊆▲
            , (λ {𝑘∈▲ →
              case ▲⊆◭₋ₐ∪◮ 𝑘∈▲ of λ
              { (inj₁ 𝑘∈◭₋ₐ) → inj₁ ∘′ proj₁ $ ◭₋ₐ⊆◭ 𝑘∈◭₋ₐ
              ; (inj₂ 𝑘∈◮) → inj₂ 𝑘∈◮ } }) ⟫
          ; (no ∄◭₋ₐ∪◮) →
            no
            λ { ⟪ ◭⊆▲ , ◮⊆▲ , ▲⊆◭∪◮ ⟫ →
            flip contradiction
            ∄◭₋ₐ∪◮
            ⟪ ◭₋ₐ⊆◭ ⟨⊆⟩ ◭⊆▲
            , ◮⊆▲
            , (λ {𝑘} 𝑘∈▲ →
              case ▲⊆◭∪◮ 𝑘∈▲ of λ
              { (inj₁ 𝑘∈◭) →
                case 𝑘 ≟ a of λ
                { (yes 𝑘≡a) → inj₂ $ subst _ (sym 𝑘≡a) a∈◮
                ; (no 𝑘≢a) → inj₁ ∘′ proj₁ $ ◭⊂◭₋ₐ|≢a 𝑘≢a 𝑘∈◭ }
              ; (inj₂ 𝑘∈◮) → inj₂ 𝑘∈◮ }) ⟫ } }
        ; (no ◭ᵃ≠◮ᵃ) →
          no
          λ { ⟪ ◭⊆▲ , ◮⊆▲ , ▲⊆◭∪◮ ⟫ →
          flip contradiction
          ◭ᵃ≠◮ᵃ
          (let ◭ᵃ=▲ᵃ = proj₂ (◭⊆▲ a∈◭)
               ◮ᵃ=▲ᵃ = proj₂ (◮⊆▲ a∈◮) in
          ◭ᵃ=▲ᵃ ⟨≡⟩ get-is-unique ⟨≡⟩ʳ ◮ᵃ=▲ᵃ) } } }
    ; (no ∄∈◭) →
      yes
      ⟪ (λ {𝑘} 𝑘∈◭ →
        flip contradiction
        ∄∈◭ $
        𝑘 , 𝑘∈◭)
      , _, refl
      , inj₂ ⟫ }
-}

module _ (m : Map) where
  open Map m

  private
    infixl 10 _≫=_
    _≫=_ : ∀ {𝑘}
              {s/x}
              {s/y}
              {s/z}
              {x : Carrier s/x}
              {y : Carrier s/y}
              {z : Carrier s/z}
              {𝑘∈x : 𝑘 ∈ x}
              (Σ𝑘∈y : ∃ λ 𝑘∈y → get 𝑘∈x ≡ get 𝑘∈y)
              (𝑘∈y→Σ𝑘∈z : (𝑘∈y : 𝑘 ∈ y) → ∃ λ 𝑘∈z → get 𝑘∈y ≡ get {m = z} 𝑘∈z)
            → ∃ λ 𝑘∈z → get 𝑘∈x ≡ get 𝑘∈z
    (𝑘∈y , xᵏ≡yᵏ) ≫= 𝑘∈y→Σ𝑘∈z
     with 𝑘∈y→Σ𝑘∈z 𝑘∈y
    ... | (𝑘∈z , yᵏ≡zᵏ) = 𝑘∈z , (xᵏ≡yᵏ ⟨≡⟩ yᵏ≡zᵏ)

    _⟨⊆⟩_ : ∀ {s/x}
              {s/y}
              {s/z}
              {x : Carrier s/x}
              {y : Carrier s/y}
              {z : Carrier s/z}
              (x⊆y : x ⊆ y)
              (y⊆z : y ⊆ z)
              → x ⊆ z
    x⊆y ⟨⊆⟩ y⊆z = _≫= y⊆z ∘ x⊆y

  record ⟦_∪_⟧ {s/◭ s/◮} (◭ : Carrier s/◭) (◮ : Carrier s/◮) : Set 𝑲𝑽 where
    constructor ⟪_,_,_⟫
    field
      {s/▲} : ℕ
      {▲} : Carrier s/▲
      ◭⊆▲ : ◭ ⊆ ▲
      ◮⊆▲ : ◮ ⊆ ▲
      ▲⊆◭∪◮ : ∀ {k} → k ∈ ▲ → (k ∈ ◭) ⊎ (k ∈ ◮)

  [_∪_] : ∀ {s/◭ s/◮} (◭ : Carrier s/◭) (◮ : Carrier s/◮) → Dec ⟦ ◭ ∪ ◮ ⟧
  [_∪_] {0} ◭ ◮ =
    yes record
      { ◭⊆▲ = λ {𝑘∈⋆ → ⊥-elim $ ∅-is-empty 𝑘∈⋆}
      ; ◮⊆▲ = _, refl
      ; ▲⊆◭∪◮ = inj₂ }
  [_∪_] {suc s/◭₋ₐ} ◭ ◮ =
    case choose ◭ of λ
    { (yes (a , a∈◭)) →
      let (◭₋ₐ , ◭₋ₐ⊆◭ , ◭⊂◭₋ₐ|≢a , a∉◭₋ₐ) = pick a∈◭ in
      case a ∈? ◮ of λ
      { (no a∉◮) →
        let (◮₊ₐ , a∈◮₊ₐ , ◮₊ₐᵃ=◭ᵃ , ◮⊆◮₊ₐ , ◮₊ₐ⊂◮|≢a) = put (get a∈◭) a∉◮ in
        case [ ◭₋ₐ ∪ ◮₊ₐ ] of λ
        { (yes ⟪ ◭₋ₐ⊆▲ , ◮₊ₐ⊆▲ , ▲⊆◭₋ₐ∪◮₊ₐ ⟫) →
          yes
          record
          { ◭⊆▲ =
            λ {𝑘} 𝑘∈◭ →
            case 𝑘 ≟ a of λ
            { (yes 𝑘≡a) →
              reright 𝑘≡a λ _ →
              let (a∈▲ , ◮₊ₐᵃ=▲ᵃ) = ◮₊ₐ⊆▲ a∈◮₊ₐ in
              a∈▲ ,
              (get-is-unique ⟨≡⟩ ◮₊ₐᵃ=◭ᵃ ʳ⟨≡⟩ ◮₊ₐᵃ=▲ᵃ)
            ; (no 𝑘≢a) → ◭⊂◭₋ₐ|≢a 𝑘≢a 𝑘∈◭ ≫= ◭₋ₐ⊆▲ }
          ; ◮⊆▲ = ◮⊆◮₊ₐ ⟨⊆⟩ ◮₊ₐ⊆▲
          ; ▲⊆◭∪◮ =
            λ {𝑘} 𝑘∈▲ →
            case ▲⊆◭₋ₐ∪◮₊ₐ 𝑘∈▲ of λ
            { (inj₁ 𝑘∈◭₋ₐ) → inj₁ ∘′ proj₁ $ ◭₋ₐ⊆◭ 𝑘∈◭₋ₐ
            ; (inj₂ 𝑘∈◮₊ₐ) →
              case 𝑘 ≟ a of λ
              { (yes 𝑘≡a) → inj₁ $ subst _ (sym 𝑘≡a) a∈◭
              ; (no 𝑘≢a) → inj₂ ∘′ proj₁ $ ◮₊ₐ⊂◮|≢a 𝑘≢a 𝑘∈◮₊ₐ } } }
        ; (no ∄◭₋ₐ∪◮₊ₐ) →
          no
          λ { ⟪ ◭⊆▲ , ◮⊆▲ , ▲⊆◭∪◮ ⟫ →
          flip contradiction
          ∄◭₋ₐ∪◮₊ₐ
          record
          { ◭⊆▲ = -- ◭₋ₐ ⊆ ▲
            ◭₋ₐ⊆◭ ⟨⊆⟩ ◭⊆▲
          ; ◮⊆▲ = -- ◮₊ₐ ⊆ ▲
            λ {𝑘} 𝑘∈◮₊ₐ →
            case 𝑘 ≟ a of λ
            { (yes 𝑘≡a) →
              reright 𝑘≡a λ _ →
              let (a∈▲ , ◮ᵃ=▲ᵃ) = ◭⊆▲ a∈◭ in
              a∈▲ ,
              (get-is-unique ⟨≡⟩ ◮₊ₐᵃ=◭ᵃ ⟨≡⟩ ◮ᵃ=▲ᵃ)
            ; (no 𝑘≢a) → ◮₊ₐ⊂◮|≢a 𝑘≢a 𝑘∈◮₊ₐ ≫= ◮⊆▲ }
          ; ▲⊆◭∪◮ = -- ▲ ⊆ ◭₋ₐ ∪ ◮₊ₐ
            λ {𝑘} 𝑘∈▲ →
            case ▲⊆◭∪◮ 𝑘∈▲ of λ
            { (inj₁ 𝑘∈◭) →
              case 𝑘 ≟ a of λ
              { (yes 𝑘≡a) → inj₂ $ subst _ (sym 𝑘≡a) a∈◮₊ₐ
              ; (no 𝑘≢a) → inj₁ ∘′ proj₁ $ ◭⊂◭₋ₐ|≢a 𝑘≢a 𝑘∈◭ }
            ; (inj₂ 𝑘∈◮) → inj₂ ∘′ proj₁ $ ◮⊆◮₊ₐ 𝑘∈◮ } } } }
      ; (yes a∈◮) →
        case get a∈◭ ≟ get a∈◮ of λ
        { (yes ◭ᵃ=◮ᵃ) →
          case [ ◭₋ₐ ∪ ◮ ] of λ
          { (yes ⟪ ◭₋ₐ⊆▲ , ◮⊆▲ , ▲⊆◭₋ₐ∪◮ ⟫) →
            yes
            ⟪ (λ {𝑘} 𝑘∈◭ →
              case 𝑘 ≟ a of λ
              { (yes 𝑘≡a) →
                reright 𝑘≡a λ _ →
                let (a∈▲ , ◮ᵃ=▲ᵃ) = ◮⊆▲ a∈◮ in
                a∈▲ , (get-is-unique ⟨≡⟩ ◭ᵃ=◮ᵃ ⟨≡⟩ ◮ᵃ=▲ᵃ)
              ; (no 𝑘≢a) → ◭⊂◭₋ₐ|≢a 𝑘≢a 𝑘∈◭ ≫= ◭₋ₐ⊆▲ })
            , ◮⊆▲
            , (λ {𝑘∈▲ →
              case ▲⊆◭₋ₐ∪◮ 𝑘∈▲ of λ
              { (inj₁ 𝑘∈◭₋ₐ) → inj₁ ∘′ proj₁ $ ◭₋ₐ⊆◭ 𝑘∈◭₋ₐ
              ; (inj₂ 𝑘∈◮) → inj₂ 𝑘∈◮ } }) ⟫
          ; (no ∄◭₋ₐ∪◮) →
            no
            λ { ⟪ ◭⊆▲ , ◮⊆▲ , ▲⊆◭∪◮ ⟫ →
            flip contradiction
            ∄◭₋ₐ∪◮
            ⟪ ◭₋ₐ⊆◭ ⟨⊆⟩ ◭⊆▲
            , ◮⊆▲
            , (λ {𝑘} 𝑘∈▲ →
              case ▲⊆◭∪◮ 𝑘∈▲ of λ
              { (inj₁ 𝑘∈◭) →
                case 𝑘 ≟ a of λ
                { (yes 𝑘≡a) → inj₂ $ subst _ (sym 𝑘≡a) a∈◮
                ; (no 𝑘≢a) → inj₁ ∘′ proj₁ $ ◭⊂◭₋ₐ|≢a 𝑘≢a 𝑘∈◭ }
              ; (inj₂ 𝑘∈◮) → inj₂ 𝑘∈◮ }) ⟫ } }
        ; (no ◭ᵃ≠◮ᵃ) →
          no
          λ { ⟪ ◭⊆▲ , ◮⊆▲ , ▲⊆◭∪◮ ⟫ →
          flip contradiction
          ◭ᵃ≠◮ᵃ
          (let ◭ᵃ=▲ᵃ = proj₂ (◭⊆▲ a∈◭)
               ◮ᵃ=▲ᵃ = proj₂ (◮⊆▲ a∈◮) in
          ◭ᵃ=▲ᵃ ⟨≡⟩ get-is-unique ⟨≡⟩ʳ ◮ᵃ=▲ᵃ) } } }
    ; (no ∄∈◭) →
      yes
      ⟪ (λ {𝑘} 𝑘∈◭ →
        flip contradiction
        ∄∈◭ $
        𝑘 , 𝑘∈◭)
      , _, refl
      , inj₂ ⟫ }
