
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (Nat to ℕ)

{- Case 1 : works as expected -}
-- postulate
--   _~_ : ℕ → ℕ → ℕ

{- Case 2 : works as expected -}
-- _~_ : Bool → Bool → Bool
-- _~_ true false = true
-- _~_ _ _ = false

{- Case 3 : doesn't work -}

_~_ : ℕ → ℕ → ℕ
_~_ = _+_

search : {t : Set} {{_ : t}} → t
search {{i}} = i

record S {t : Set} (_~_ : t → t → t) : Set where
  field
    {{~-com}} : ∀ a b → a ~ b ≡ b ~ a

open S ⦃ … ⦄

postulate
  instance +s : S _+_

eg : ∀ a b → a + b ≡ b + a
eg = ~-com


-- f : ∀ {a b} → a ~s b ≡ b ~s a
-- f {a} {b} = search ⦃ ~-coms {a} {b} ⦄ -- coerce {!!} -- (search)


-- record Coerced {X : Set} (F : X → X → X) : Set where
--   field G : X → X → X

-- record Commutativity′ {X : Set} (F : X → X → Set) : Set where
--   field
--     commutativity : ∀ {a b} → F a b

-- open Commutativity′ ⦃ … ⦄

-- Commutativity : {X : Set} (op : X → X → X) → Set
-- Commutativity op = Commutativity′ (λ a b → op a b ≡ op b a)

-- abstract _~_ = _+_

-- postulate instance com-~ : Commutativity _~_

-- postulate coerce : ∀ a {b} → a ~ b ≡ b ~ a → a + b ≡ b + a
-- postulate coerce' : ∀ {a} {b} → a + b ≡ b + a → a ~ b ≡ b ~ a

-- ff : ∀ {a b} → a ~ b ≡ b ~ a
-- ff = commutativity

-- gg : ∀ {a b} → a + b ≡ b + a
-- gg {a} {b} = (coerce a commutativity) -- (commutativity)

-- postulate foo : ∀ {a b} → a + b ≡ b + a

-- bar : ∀ {a b} → a + b ≡ b + a
-- bar = gg -- coerce _ ff

-- qux : ∀ {a b} → a ~ b ≡ b ~ a
-- qux = ff -- coerce' gg





-- -- -- record S {t : Set} (_~_ : t → t → t) : Set where
-- -- --   field
-- -- --     {{~-com}} : ∀ {a b} → a ~ b ≡ b ~ a

-- -- -- open S ⦃ … ⦄

-- -- -- record T (t : Set) a b : Set where
-- -- --   field
-- -- --     _~'_ : t → t → t
-- -- --     -- {{~-com'}} : a ~ b ≡ b ~ a
-- -- --     s-it : a ~' b ≡ b ~' a

-- -- -- open T ⦃ … ⦄

-- -- -- {-
-- -- -- s-it : ∀ {t : Set} {a b : t} {_~'_} → ⦃ _ : S _~'_ ⦄ → a ~' b ≡ b ~' a
-- -- -- s-it = search
-- -- -- -}
-- -- -- {-
-- -- -- postulate
-- -- --   -- instance +s : S _+_
-- -- --   instance +t : ∀ {a b} → T _~_ a b
-- -- -- -}

-- -- -- instance +t : ∀ {a b} → T ℕ a b
-- -- -- T._~'_ +t = _~_
-- -- -- T.s-it +t = {!!}

-- -- -- eg : ∀ {a b} → a + b ≡ b + a
-- -- -- eg {a} {b} = s-it
-- -- -- {-
-- -- --   where
-- -- --     go : ∀ {_~_} → ⦃ _ : S _~_ ⦄ → a ~ b ≡ b ~ a
-- -- --     go = search
-- -- -- -}


-- -- -- -- postulate
-- -- -- --   instance
-- -- -- --     ~-com : ∀ {a b} → a ~ b ≡ b ~ a

-- -- -- -- foo : ∀ {a b} → a ~ b ≡ b ~ a
-- -- -- -- foo {a} {b} = go {_~'_ = _~_} {a = a} {b = b} ⦃ ~-com {a} {b} ⦄ where
-- -- -- --   go : ∀ {t : Set} {_~'_ : t → t → t} {a b : t} ⦃ _ : a ~' b ≡ b ~' a ⦄ → a ~' b ≡ b ~' a
-- -- -- --   go = search



-- -- -- -- -- open import Agda.Builtin.Equality
-- -- -- -- -- open import Agda.Builtin.Bool

-- -- -- -- -- f : Bool → Bool → Bool -- rejected
-- -- -- -- -- f true true = true
-- -- -- -- -- -- f _ _  = false
-- -- -- -- -- f false true = false
-- -- -- -- -- f true false = false
-- -- -- -- -- f false false = false

-- -- -- -- -- postulate
-- -- -- -- --   eq : ∀ {a b} → f a b ≡ f b a

-- -- -- -- -- test : ∀ {a b} → f a b ≡ f b a
-- -- -- -- -- test {a} {b} = {!eq!}

-- -- -- -- -- {-
-- -- -- -- -- _19 := λ {a} {b} → eq {?0 {a} {b}} {?1 {a} {b}} [blocked by problem 22]
-- -- -- -- -- [22,26] (f (?1 {a} {b}) (?0 {a} {b})) = (f b a) : Bool
-- -- -- -- -- [22,25] (f (?0 {a} {b}) (?1 {a} {b})) = (f a b) : Bool

-- -- -- -- -- ?0 {a} {b} := true, ?1 {a} {b} = f a b

-- -- -- -- -- [22,26] (f (f a b) true) = (f b a) : Bool
-- -- -- -- -- [22,25] (f true (f a b)) = (f a b) : Bool
-- -- -- -- -- [22,25] (f a b) = (f a b) : Bool




-- -- -- -- -- -}

-- -- -- -- -- {-
-- -- -- -- -- _~₁_ : Bool → Bool → Bool -- accepted
-- -- -- -- -- _~₁_ true true = true
-- -- -- -- -- _~₁_ _ _ = false

-- -- -- -- -- postulate
-- -- -- -- --   eq₁ : ∀ {a b} → a ~₁ b ≡ b ~₁ a

-- -- -- -- -- test₁ : ∀ {a b} → a ~₁ b ≡ b ~₁ a
-- -- -- -- -- test₁ = {!eq₁!} -- okay
-- -- -- -- -- -}

-- -- -- -- -- -- _~₂_ : Bool → Bool → Bool -- rejected
-- -- -- -- -- -- _~₂_ true true = true
-- -- -- -- -- -- _~₂_ false true = false
-- -- -- -- -- -- _~₂_ true false = false
-- -- -- -- -- -- _~₂_ false false = false

-- -- -- -- -- -- postulate
-- -- -- -- -- --   eq₂ : ∀ {a b} → a ~₂ b ≡ b ~₂ a

-- -- -- -- -- -- test₂ : ∀ {a b} → a ~₂ b ≡ b ~₂ a
-- -- -- -- -- -- test₂ {a} {b} = eq₂ {a = {!!}} {b = {!!}} -- okay







-- -- -- -- -- -- -- open import Agda.Builtin.Equality
-- -- -- -- -- -- -- open import Agda.Builtin.Bool
-- -- -- -- -- -- -- open import Agda.Builtin.Nat renaming (Nat to ℕ)

-- -- -- -- -- -- -- {- Case 1 : works as expected -}
-- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- --   _~_ : ℕ → ℕ → ℕ

-- -- -- -- -- -- -- {- Case 2 : works as expected -}
-- -- -- -- -- -- -- -- _~_ : Bool → Bool → Bool
-- -- -- -- -- -- -- -- _~_ true false = true
-- -- -- -- -- -- -- -- _~_ _ _ = false

-- -- -- -- -- -- -- {- Case 3 : doesn't work -}
-- -- -- -- -- -- -- _~_ : ℕ → ℕ → ℕ
-- -- -- -- -- -- -- _~_ = _+_


-- -- -- -- -- -- -- postulate
-- -- -- -- -- -- --   instance
-- -- -- -- -- -- --     ~-com : ∀ {a b} → a ~ b ≡ b ~ a

-- -- -- -- -- -- -- search : {t : Set} {{_ : t}} → t
-- -- -- -- -- -- -- search {{i}} = i

-- -- -- -- -- -- -- open import Prelude.Function using (id)

-- -- -- -- -- -- -- f : ∀ {a b} → a ~ b ≡ b ~ a
-- -- -- -- -- -- -- f {a} {b} = ~-com {a = {!!}} {b = {!!}}

-- -- -- -- -- -- -- -- g: ∀ {a b} {a' : ℕ → ℕ → ℕ} {

-- -- -- -- -- -- -- -- foo : {x : ℕ} {y : ℕ} → x + y ≡ y + x
-- -- -- -- -- -- -- -- foo {zero} {zero} = refl
-- -- -- -- -- -- -- -- foo {zero} {suc y} = {!!}
-- -- -- -- -- -- -- -- foo {suc x} {zero} = {!!}
-- -- -- -- -- -- -- -- foo {suc x} {suc y} = {!foo {x} {suc y}!}

-- -- -- -- -- -- -- -- bar : {a₁ : ℕ} {b₁ : ℕ} → a₁ + b₁ ≡ b₁ + a₁
-- -- -- -- -- -- -- -- bar = foo
-- -- -- -- -- -- -- -- -- search

-- -- -- -- -- -- -- -- open import Agda.Builtin.Equality
-- -- -- -- -- -- -- -- open import Agda.Builtin.Bool

-- -- -- -- -- -- -- -- _~₁_ : Bool → Bool → Bool
-- -- -- -- -- -- -- -- _~₁_ true true = true
-- -- -- -- -- -- -- -- _~₁_ _ _ = false

-- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- --   eq₁ : ∀ {a b} → a ~₁ b ≡ b ~₁ a

-- -- -- -- -- -- -- -- test₁ : ∀ {a b} → a ~₁ b ≡ b ~₁ a
-- -- -- -- -- -- -- -- test₁ = eq₁ -- okay

-- -- -- -- -- -- -- -- _~₂_ : Bool → Bool → Bool
-- -- -- -- -- -- -- -- _~₂_ true true = true
-- -- -- -- -- -- -- -- _~₂_ false true = false
-- -- -- -- -- -- -- -- _~₂_ true false = false
-- -- -- -- -- -- -- -- _~₂_ false false = false

-- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- --   eq₂ : ∀ {a b} → a ~₂ b ≡ b ~₂ a

-- -- -- -- -- -- -- -- test₂ : ∀ {a b} → a ~₂ b ≡ b ~₂ a
-- -- -- -- -- -- -- -- test₂ = eq₂ -- yellow

-- -- -- -- -- -- -- -- abstract

-- -- -- -- -- -- -- --   _~₃_ : Bool → Bool → Bool
-- -- -- -- -- -- -- --   _~₃_ true true = true
-- -- -- -- -- -- -- --   _~₃_ false true = false
-- -- -- -- -- -- -- --   _~₃_ true false = false
-- -- -- -- -- -- -- --   _~₃_ false false = false

-- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- --   eq₃ : ∀ {a b} → a ~₃ b ≡ b ~₃ a

-- -- -- -- -- -- -- -- test₃ : ∀ {a b} → a ~₃ b ≡ b ~₃ a
-- -- -- -- -- -- -- -- test₃ = eq₃ -- okay

-- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- ———— Errors ————————————————————————————————————————————————
-- -- -- -- -- -- -- -- Failed to solve the following constraints:
-- -- -- -- -- -- -- --   _38 := λ {.a} {.b} → eq₂ [blocked on problem 48]
-- -- -- -- -- -- -- --   [48, 52] _b_37 ~₂ _a_36 = .b ~₂ .a : Bool
-- -- -- -- -- -- -- --   [48, 51] _a_36 ~₂ _b_37 = .a ~₂ .b : Bool
-- -- -- -- -- -- -- -- -}
