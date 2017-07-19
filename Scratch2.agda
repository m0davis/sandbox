module Scratch2 where

module _ {A : Set} (_+_ : A → A → A) (let infixl 5 _+_; _+_ = _+_) where
  foo : A → A → A → A
  foo w x y = w + x + y


-- {-# OPTIONS --show-implicit #-}

-- record Class1 (A : Set) : Set where no-eta-equality
-- record Class2 : Set where no-eta-equality

-- module _
--   {A : Set}
--   where

--   postulate
--     instance toplevelClass1Instance : ∀ {x} → Class1 x
--     instance toplevelClass1Instance' : ∀ {x} → Class1 x
--     instance toplevelClass2Instance : Class2

--   module _
--     ⦃ lambdaboundClass1Instance : Class1 A ⦄
--     ⦃ lambdaboundClass2Instance : Class2 ⦄
--     (f : ⦃ c1' : {A' : Set} → Class1 A' ⦄ → A)
--     (P : A → Set)
--     where

--     postulate
--       test-unconstrained-metavariables-failure : P f

-- -- {-# OPTIONS --show-implicit #-}

-- -- record Class1 (A : Set) : Set where no-eta-equality
-- -- record Class2 : Set where no-eta-equality

-- -- module _
-- --   {A : Set}
-- --   where

-- --   postulate
-- --     instance toplevelClass2Instance : Class2

-- --   module _
-- --     ⦃ lambdaboundClass1Instance : Class1 A ⦄
-- --     ⦃ lambdaboundClass2Instance : Class2 ⦄
-- --     (f : {A' : Set} ⦃ c1' : Class1 A' ⦄ → A)
-- --     (P : A → Set)
-- --     where

-- --     postulate
-- --       test-unconstrained-metavariables-failure : P f

-- -- {-
-- -- Resolve instance argument _c1'_8 : ({A = A₁ : Set}
-- --        {{lambdaboundClass1Instance = lambdaboundClass1Instance₁
-- --          : Class1 A₁}}
-- --        {{lambdaboundClass2Instance = lambdaboundClass2Instance₁ : Class2}}
-- --        (f₁ : {A' : Set} {{c1' : Class1 A'}} → A₁) (P₁ : A₁ → Set) →
-- --        Class1
-- --        (_A'_7 {A₁} {{lambdaboundClass1Instance₁}}
-- --         {{lambdaboundClass2Instance₁}} f₁ P₁)).
-- --   Candidates:
-- --     [ lambdaboundClass2Instance : Class2
-- --     , lambdaboundClass1Instance : (Class1 A) ]
-- -- -}



-- -- -- open import Agda.Primitive
-- -- -- open import Data.Empty using (⊥)
-- -- -- open import Data.Unit using (⊤)
-- -- -- open import Relation.Binary
-- -- -- open import Relation.Binary.PropositionalEquality using (_≡_)
-- -- -- import Relation.Binary.PropositionalEquality as PropEq

-- -- -- data Sort : Set where
-- -- --     stmt expr item lit : Sort

-- -- -- data _≤_ : Rel Sort lzero where
-- -- --     refl : {a : Sort} → a ≤ a
-- -- --     trans : {a b c : Sort} → a ≤ b → b ≤ c → a ≤ c
-- -- --     lit≤expr  : lit  ≤ expr
-- -- --     expr≤stmt : expr ≤ stmt
-- -- --     item≤stmt : item ≤ stmt

-- -- -- ≤-antisymmetric : Antisymmetric _≡_ _≤_
-- -- -- ≤-antisymmetric refl y≤x = PropEq.refl
-- -- -- ≤-antisymmetric (trans x≤i i≤y) y≤x = {!!}
-- -- -- ≤-antisymmetric lit≤expr (trans y≤x refl) = {!!}
-- -- -- ≤-antisymmetric lit≤expr (trans y≤x (trans y≤x₁ y≤x₂)) = {!!}
-- -- -- ≤-antisymmetric expr≤stmt y≤x = {!!}
-- -- -- ≤-antisymmetric item≤stmt y≤x = {!!}


-- -- -- --     λ { refl _ → PropEq.refl;
-- -- -- --         _ refl → PropEq.refl;
-- -- -- --         (trans refl x≤y) y≤x → ≤-antisymmetric x≤y y≤x;
-- -- -- --         (trans x≤y refl) y≤x → ≤-antisymmetric x≤y y≤x;
-- -- -- --         x≤y (trans refl y≤x) → ≤-antisymmetric x≤y y≤x;
-- -- -- --         x≤y (trans y≤x refl) → ≤-antisymmetric x≤y y≤x;
-- -- -- --         x≤z (trans z≤y (trans y≤w w≤x)) → {!!} }

-- -- -- -- -- record Type₁ : Set where

-- -- -- -- -- record Type₂ : Set where

-- -- -- -- -- record Aggregator : Set where
-- -- -- -- --   field
-- -- -- -- --     {{i₁}} : Type₁
-- -- -- -- --     {{i₂}} : Type₂

-- -- -- -- -- postulate
-- -- -- -- --   instance
-- -- -- -- --     type₁ : Type₁
-- -- -- -- --     type₂ : Type₂

-- -- -- -- -- agg : Aggregator
-- -- -- -- -- agg = record {
-- -- -- -- --     i₂ = {!!} -- goal: Type₁
-- -- -- -- --   }

-- -- -- -- -- -- open import Scratch

-- -- -- -- -- -- open import Agda.Primitive

-- -- -- -- -- -- record Category 𝔬 𝔪 𝔮 : Set (lsuc (𝔬 ⊔ 𝔪 ⊔ 𝔮)) where
-- -- -- -- -- --   field
-- -- -- -- -- --     semigroupoid : Semigroupoid 𝔬 𝔪 𝔮

-- -- -- -- -- --   open Semigroupoid semigroupoid

-- -- -- -- -- --   instance _ = λ {x} {y} → x ⇒ y
-- -- -- -- -- --   open Setoid ⦃ … ⦄ using (_≋_)

-- -- -- -- -- --   field
-- -- -- -- -- --     ε : ∀ {x} → x ↦ x
-- -- -- -- -- --     left-identity : ∀ {x y} (f : x ↦ y) → ε ∙ f ≋ f
-- -- -- -- -- --     right-identity : ∀ {x y} (f : x ↦ y) → f ∙ ε ≋ f

-- -- -- -- -- -- _⇒_ : ∀ {a} (A : Set a) {b} (B : Set b) → Setoid _ _
-- -- -- -- -- -- _⇒_ A B = Setoid≡̇ {A = A} λ _ → B

-- -- -- -- -- -- postulate
-- -- -- -- -- --   X : Set
-- -- -- -- -- --   F : X → Set
-- -- -- -- -- --   T : X → Set
-- -- -- -- -- --   _◇_ : ∀ {y z} →
-- -- -- -- -- --           ((x : F y) → T z) → ∀ {x} → ((x₁ : F x) → T y) → (x₁ : F x) → T z
-- -- -- -- -- --   ε : ∀ {x} (x₁ : F x) → T x

-- -- -- -- -- -- SemigroupoidSubstitution : Semigroupoid _ _ _
-- -- -- -- -- -- Semigroupoid.⋆ SemigroupoidSubstitution = _
-- -- -- -- -- -- Semigroupoid._⇒_ SemigroupoidSubstitution m n = F m ⇒ T n -- Fin m ⇒ Term n
-- -- -- -- -- -- Semigroupoid._∙_ SemigroupoidSubstitution = _◇_ -- _◇_
-- -- -- -- -- -- Semigroupoid.associativity SemigroupoidSubstitution = {!!} -- ◇-associativity
-- -- -- -- -- -- Semigroupoid.extensionality SemigroupoidSubstitution = {!!} -- ◇-extensionality

-- -- -- -- -- -- CategorySubstitution : Category _ _ _
-- -- -- -- -- -- Category.semigroupoid CategorySubstitution = SemigroupoidSubstitution --
-- -- -- -- -- -- Category.ε CategorySubstitution = ε -- ε
-- -- -- -- -- -- Category.left-identity CategorySubstitution = {!!}
-- -- -- -- -- -- Category.right-identity CategorySubstitution = {!!} -- {x} {y} {f} x₁ = ? -- ◇-right-identity f x₁

-- -- -- -- -- -- test-right-id = {!Category.right-identity CategorySubstitution!}


-- -- -- -- -- -- -- --{-# OPTIONS --allow-unsolved-metas #-}

-- -- -- -- -- -- -- open import Agda.Builtin.Nat

-- -- -- -- -- -- -- infix 4 _≤_
-- -- -- -- -- -- -- data _≤_ : Nat → Nat → Set where
-- -- -- -- -- -- --   m≤m : ∀ m → m ≤ m
-- -- -- -- -- -- --   m≤sm : ∀ m n → m ≤ n → m ≤ suc n

-- -- -- -- -- -- -- foo-lish : ∀ m n → m ≤ 2 * n → m ≤ 1 * n
-- -- -- -- -- -- -- foo-lish m zero x = {!!}
-- -- -- -- -- -- -- foo-lish m (suc n) x = foo-lish m {!suc n!} x

-- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- Proposal: add agda2-show-unsolved-metas

-- -- -- -- -- -- -- `C-c C-l` in emacs helpfully shows us the unsolved metasvariables' types and source locations, as well as the unsolved constraints.

-- -- -- -- -- -- -- The unsolved metas:
-- -- -- -- -- -- -- ```
-- -- -- -- -- -- -- _20 : m ≤ ?1 m n x + (?1 m n x + zero)  [ at Foolish.agda:12,41-42 ]
-- -- -- -- -- -- -- _21 : m ≤ ?1 m n x + (?1 m n x + zero)  [ at Foolish.agda:12,41-42 ]
-- -- -- -- -- -- -- _22 : m ≤ suc (n + zero)  [ at Foolish.agda:12,24-42 ]
-- -- -- -- -- -- -- _23 : m ≤ suc (n + zero)  [ at Foolish.agda:12,24-42 ]
-- -- -- -- -- -- -- ```
-- -- -- -- -- -- -- And the unsolved constraints:
-- -- -- -- -- -- -- ```
-- -- -- -- -- -- -- ———— Errors ————————————————————————————————————————————————
-- -- -- -- -- -- -- Failed to solve the following constraints:
-- -- -- -- -- -- --   _22 := λ m n x → foo-lish m (?1 m n x) (_21 m n x)
-- -- -- -- -- -- --     [blocked on problem 30]
-- -- -- -- -- -- --   [30, 32] ?1 m n x + 0 * ?1 m n x = suc (n + 0 * suc n) : Nat
-- -- -- -- -- -- --   _20 := (λ m n x → x) [blocked on problem 27]
-- -- -- -- -- -- --   [27, 29] (suc (n + 1 * suc n)) = (?1 m n x + 1 * ?1 m n x) : Nat
-- -- -- -- -- -- -- ```
-- -- -- -- -- -- -- After loading, `C-c C-=` (`agda2-show-constraints`) shows only the unsolved constraints, not the unsolved metavariables. Thus we lose some of the metavariables, as well as all of their types and source code locations. There doesn't seem to be any way to recover that information other than reloading.

-- -- -- -- -- -- -- Under this proposal, `C-c C--` would show all the unsolved metas, including source locations (perhaps under a new function, `agda2-show-unsolved-metas`). Alternatively, change `agda2-show-constraints` to `agda2-show-unsolved-metas-and-constraints`.
-- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- postulate D : Set

-- -- -- -- -- -- -- -- record R : Set₁ where
-- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- --     r : Set

-- -- -- -- -- -- -- -- open R {{ ... }} public

-- -- -- -- -- -- -- -- instance iR : R
-- -- -- -- -- -- -- -- iR = record { r = D }
