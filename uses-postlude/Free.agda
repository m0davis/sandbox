module Free where
  open import Postlude

  data Free {𝑨} (F : Set 𝑨 → Set 𝑨) (A : Set 𝑨) : Set (sucₗ 𝑨) where
    pure : A → Free F A
    free : ∀ {𝑎 : Set 𝑨} → (𝑎 → Free F A) → F 𝑎 → Free F A

  module FreeComparison {α} {A : Set α} {{_ : Eq A}}
    where

    data _≞_ : Free List A → Free List A → Set (sucₗ α) where
      Pure : {x : A} → {y : A} → x ≡ y → pure x ≞ pure y
      Free[] : ∀ {x y : Set α} → (fx : x → Free List A) → (fy : y → Free List A) → free fx [] ≞ free fy []
      Free∷ : ∀ {x y : Set α} → {fx : x → Free List A} → {x' : x} {xs : List x} → {fy : y → Free List A} → {y' : y} {ys : List y} → fx x' ≞ fy y' → free fx xs ≞ free fy ys → free fx (x' ∷ xs) ≞ free fy (y' ∷ ys)

    _≞?_ : (flx : Free List A) → (fly : Free List A) → Dec (flx ≞ fly)
    pure x ≞? pure y with x ≟ y
    ... | yes x≡y rewrite x≡y = yes (Pure refl)
    ... | no x≢y = no (λ { (Pure x≡y) → x≢y x≡y })
    pure _ ≞? free _ _ = no (λ ())
    free _ _ ≞? pure _ = no (λ ())
    free fx [] ≞? free fy [] = yes (Free[] fx fy)
    free fx [] ≞? free fy (y ∷ ys) = no (λ ())
    free fx (x ∷ xs) ≞? free fy [] = no (λ ())
    free fx (x ∷ xs) ≞? free fy (y ∷ ys) with fx x ≞? fy y
    free fx (x ∷ xs) ≞? free fy (y ∷ ys) | yes fxx≞fyy with free fx xs ≞? free fy ys
    free fx (x ∷ xs) ≞? free fy (y ∷ ys) | yes fxx≞fyy | yes freefxxs≞freefyys = yes (Free∷ fxx≞fyy freefxxs≞freefyys)
    free fx (x ∷ xs) ≞? free fy (y ∷ ys) | yes fxx≞fyy | no freefxxs≞freefyys = no (λ { (Free∷ x₁ x₂) → freefxxs≞freefyys x₂ })
    free fx (x ∷ xs) ≞? free fy (y ∷ ys) | no fxx≞fyy = no (λ { (Free∷ x₁ x₂) → fxx≞fyy x₁ })

    pure≞ : ∀ {x : A} → pure x ≞ pure x
    pure≞ = Pure refl

    empty≞ : ∀ {M N : Set α} → {f : M → Free List A} → {g : N → Free List A} → free f [] ≞ free g []
    empty≞ {f = f} {g = g} = Free[] f g

    data _⋒_ : (X : Free List A) → (Y : Free List A) → Set (sucₗ α) where
      Equal : ∀ {X : Free List A} {Y : Free List A} → X ≞ Y → X ⋒ Y
      Pure : {x : A} → {y : A} → x ≢ y → pure x ⋒ pure y
      PureFree : (x : A) → ∀ {N : Set α} → (g : N → Free List A) → (ns : List N) → pure x ⋒ free g ns
      FreePure : ∀ {M : Set α} → (f : M → Free List A) → (ms : List M) → (y : A) → free f ms ⋒ pure y
      Free∷Free[] : ∀ {M N : Set α} → (f : M → Free List A) → (ms : List M) → (g : N → Free List A) → free f ms ⋒ free g []
      Free[]Free∷ : ∀ {M N : Set α} → (f : N → Free List A) → (g : M → Free List A) → (ns : List M) → free f [] ⋒ free g ns
      Free∷Free∷ : ∀ {M N : Set α} → {f : M → Free List A} → {m : M} {ms : List M} → {g : N → Free List A} → {n : N} {ns : List N} → ¬ free f (m ∷ ms) ≞ free g (n ∷ ns) → f m ⋒ g n → free f ms ⋒ free g ns → free f (m ∷ ms) ⋒ free g (n ∷ ns)

    diff : (X : Free List A) → (Y : Free List A) → X ⋒ Y
    diff (pure x) (pure y) with x ≟ y
    diff (pure x) (pure y) | yes p rewrite p = Equal pure≞
    diff (pure x) (pure y) | no ¬p = Pure ¬p
    diff (pure x) (free g ns) = PureFree x g ns
    diff (free f ms) (pure y) = FreePure f ms y
    diff (free f []) (free g []) = Equal empty≞
    diff (free f []) (free g (n ∷ ns)) = Free[]Free∷ f g (n ∷ ns)
    diff (free f (m ∷ ms)) (free g []) = Free∷Free[] f (m ∷ ms) g
    diff (free f (m ∷ ms)) (free g (n ∷ ns)) with free f (m ∷ ms) ≞? free g (n ∷ ns)
    diff (free f (m ∷ ms)) (free g (n ∷ ns)) | yes p = Equal p
    diff (free f (m ∷ ms)) (free g (n ∷ ns)) | no ¬p = Free∷Free∷ ¬p (diff (f m) (g n)) (diff (free f ms) (free g ns))
{-
    diff' : (X : Free List A) → (Y : Free List A) → X ⋒ Y
    diff' X Y = Equal {!!}

    left : ∀ {X : Free List A} {Y : Free List A} → X ⋒ Y → Free List A
    left {X = X} _ = X

    right : ∀ {X : Free List A} {Y : Free List A} → X ⋒ Y → Free List A
    right {Y = Y} _ = Y

    diffLaw : (X : Free List A) → (Y : Free List A) → ∃ λ (X⋒Y : X ⋒ Y) → left X⋒Y ≞ X × right X⋒Y ≞ Y
    diffLaw (pure x) (pure y) with x ≟ y
    diffLaw (pure x) (pure y) | yes p rewrite p = (diff (pure y) (pure y)) , pure≞ , pure≞
    diffLaw (pure x) (pure y) | no ¬p = {!!}
    diffLaw (pure x₁) (free x₂ x₃) = {!!}
    diffLaw (free x₁ x₂) (pure x₃) = {!!}
    diffLaw (free x₁ x₂) (free x₃ x₄) = {!!}
-}
    data _⋐_ : (X : Free List A) {Y : Free List A} (X⋒Y : X ⋒ Y) → Set (sucₗ α) where
      Equal : ∀ {X : Free List A} {Y : Free List A} (X≞Y : X ≞ Y) → X ⋐ Equal X≞Y
      PureFree : (x : A) → ∀ {N : Set α} → (g : N → Free List A) → (ns : List N) → pure x ⋐ PureFree x g ns
      Free∷Free∷ : {M N : Set α} →
                   {f : M → Free List A} →
                   {m : M} {ms : List M} →
                   {g : N → Free List A} →
                   {n : N} {ns : List N} →
                   (notequal : ¬ free f (m ∷ ms) ≞ free g (n ∷ ns)) →
                   {first : f m ⋒ g n} →
                   {rest : free f ms ⋒ free g ns} →
                   f m ⋐ first →
                   free f ms ⋐ rest →
                   free f (m ∷ ms) ⋐ Free∷Free∷ notequal first rest

    match : ∀ {X : Free List A} {Y : Free List A} (X⋒Y : X ⋒ Y) → Dec (X ⋐ X⋒Y)
    match (Equal X≞Y) = yes $ Equal X≞Y
    match (Pure x₂) = yes $ {!Equal!}
    match (PureFree x g ns) = yes $ PureFree x g ns
    match (FreePure f ms y) = no (λ ())
    match (Free∷Free[] f ms g) = {!!}
    match (Free[]Free∷ f g ns) = {!!}
    match (Free∷Free∷ x₁ X⋒Y X⋒Y₁) = {!!}

    data _⋐'_ : (X : Free List A) {Y : Free List A} (X⋒Y : X ⋒ Y) → Set (sucₗ α) where

      Equal : ∀ {X : Free List A} {Y : Free List A} (X≞Y : X ≞ Y) → X ⋐' Equal X≞Y
      PureFree : (x : A) → ∀ {N : Set α} → (g : N → Free List A) → (ns : List N) → pure x ⋐' PureFree x g ns
      Free∷Free∷ : {M N : Set α} →
                   {f : M → Free List A} →
                   {m : M} {ms : List M} →
                   {g : N → Free List A} →
                   {n : N} {ns : List N} →
                   (notequal : ¬ free f (m ∷ ms) ≞ free g (n ∷ ns)) →
                   {first : f m ⋒ g n} →
                   {rest : free f ms ⋒ free g ns} →
                   f m ⋐' first →
                   free f ms ⋐' rest →
                   free f (m ∷ ms) ⋐' Free∷Free∷ notequal first rest

    match' : ∀ {X : Free List A} {Y : Free List A} (X⋒Y : X ⋒ Y) → Dec (X ⋐' X⋒Y)
    match' = ?

    data _∈pf_ : (a : A) → {X : Free List A} {Y : Free List A} {X⋒Y : X ⋒ Y} (X⋐X⋒Y : X ⋐ X⋒Y) → Set (sucₗ α) where
      singleton : (a : A) → ∀ {N : Set α} → (g : N → Free List A) → (ns : List N)→ a ∈pf PureFree a g ns
      descend1 : ∀ (a : A) → {M N : Set α} →
                   {f : M → Free List A} →
                   {m : M} {ms : List M} →
                   {g : N → Free List A} →
                   {n : N} {ns : List N} →
                   {notequal : ¬ free f (m ∷ ms) ≞ free g (n ∷ ns)} →
                   {first : f m ⋒ g n} →
                   {rest : free f ms ⋒ free g ns} →
                   {fm⋐first : f m ⋐ first} →
                   {freefms⋐rest : free f ms ⋐ rest}
                   (a∈pffirst : a ∈pf fm⋐first) →
                   a ∈pf Free∷Free∷ notequal fm⋐first freefms⋐rest
      descend2 : (a : A) {M N : Set α} →
                   {f : M → Free List A} →
                   {m : M} {ms : List M} →
                   {g : N → Free List A} →
                   {n : N} {ns : List N} →
                   {notequal : ¬ free f (m ∷ ms) ≞ free g (n ∷ ns)} →
                   {first : f m ⋒ g n} →
                   {rest : free f ms ⋒ free g ns} →
                   {fm⋐first : f m ⋐ first} →
                   {freefms⋐rest : free f ms ⋐ rest}
                   (a∈pffirst : a ∈pf freefms⋐rest) →
                   a ∈pf Free∷Free∷ notequal fm⋐first freefms⋐rest

    getpf : ∀ {a : A} {X : Free List A} {Y : Free List A} {X⋒Y : X ⋒ Y} {X⋐X⋒Y : X ⋐ X⋒Y} → (a ∈pf X⋐X⋒Y) → Free List A
    getpf (singleton a g ns) = free g ns
    getpf (descend1 a x) = getpf x
    getpf (descend2 a x) = getpf x

    _∈pf?_ : (a : A) {X : Free List A} {Y : Free List A} {X⋒Y : X ⋒ Y} (X⋐X⋒Y : X ⋐ X⋒Y) → Dec (a ∈pf X⋐X⋒Y)
    _∈pf?_ a (Equal X≞Y) = no (λ ())
    _∈pf?_ a (PureFree x g ns) with a ≟ x
    _∈pf?_ a (PureFree .a g ns) | yes refl = yes (singleton a g ns)
    _∈pf?_ a  (PureFree x g ns) | no a≢x = no (foo a≢x) where
      foo : ∀ {a : A} → {x : A} → {N : Set α} → {g : N → Free List A} → {ns : List N} (a≢x : ¬ (a ≡ x)) → ¬ a ∈pf PureFree x g ns
      foo a≢x (singleton a g ns) = a≢x refl
    _∈pf?_ a (Free∷Free∷ notequal X⋐X⋒Y X⋐X⋒Ys) with a ∈pf? X⋐X⋒Y
    _∈pf?_ a (Free∷Free∷ notequal X⋐X⋒Y X⋐X⋒Ys) | yes x = yes (descend1 a x)
    _∈pf?_ a (Free∷Free∷ notequal X⋐X⋒Y X⋐X⋒Ys) | no x with a ∈pf? X⋐X⋒Ys
    _∈pf?_ a (Free∷Free∷ notequal X⋐X⋒Y X⋐X⋒Ys) | no x | yes y = yes (descend2 a y)
    _∈pf?_ a (Free∷Free∷ notequal X⋐X⋒Y X⋐X⋒Ys) | no x | no y = no (λ { (descend1 .a x₁) → x x₁ ; (descend2 .a x₁) → y x₁ })
