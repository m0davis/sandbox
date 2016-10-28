--{-# OPTIONS --show-implicit #-}
module Scratch where

-- module OnlyFastInSharing where
--   open import Agda.Builtin.Nat
--   open import Agda.Builtin.Equality

--   case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
--   case x of f = f x

--   pow2 : Nat → Nat
--   pow2 0 = 1
--   pow2 (suc n) = -- (λ {r → r + r}) (pow2 n)
--                  case pow2 n of λ {r → r + r} -- fast
--                  -- (λ r → r + r) (pow2 n) -- slow

--   test : pow2 20 ≡ 1048576
--   test = refl

-- {-
-- pow2 6
-- case pow2 5 of λ r → r + r
-- (λ r → r + r) (pow2 5)
-- pow2 5 + pow2 5
-- now pow2 5 gets reduced only once due to --sharing

-- pow2 6
-- (λ r → r + r) (pow2 5)
-- pow2 5 + pow2 5

-- -}

-- -- module OnlyFastInHaskell where
-- --   open import Agda.Builtin.Nat
-- --   open import Agda.Builtin.Equality
-- --   pow2 : Nat → Nat
-- --   pow2 0 = 1
-- --   pow2 (suc n) = r + r
-- --     where r = pow2 n

-- --   test : pow2 20 ≡ 1048576
-- --   test = {!refl!}

-- {-
-- pow2 6
-- r 6 + r 6
-- pow2 5 + pow2 5
-- -}

-- -- -- -- -- module InconsistencyFromLambdaNaming where

-- -- -- -- --   open import Prelude.Memoization

-- -- -- -- --   open import Prelude.Product
-- -- -- -- --   open import Prelude.Equality
-- -- -- -- --   open import Prelude.Function

-- -- -- -- --   open import Agda.Builtin.Nat using (Nat; suc; zero)

-- -- -- -- --   foo : (n : Nat) → Nat × Mem n
-- -- -- -- --   foo zero = zero , (zero , refl)
-- -- -- -- --   foo (suc n) =
-- -- -- -- --     case foo n of λ
-- -- -- -- --     { (foon , (n' , n'≡n)) →
-- -- -- -- --       foon , (suc n' , cong suc {!!}) }

-- -- -- -- --   postulate
-- -- -- -- --     mem : (n : Nat) → Mem n

-- -- -- -- --   bar : (n : Nat) → n ≡ n
-- -- -- -- --   bar zero = {!!}
-- -- -- -- --   bar (suc n) = case mem n of λ { (n' , n'≡n) → {!!} }

-- -- -- -- -- -- --   _+_ : (n : Nat) → (m : Nat) → Nat × Mem n × Mem m
-- -- -- -- -- -- --   zero  + m = m , (zero , refl) , (m , refl)
-- -- -- -- -- -- --   suc n + m =
-- -- -- -- -- -- --     case n + m of λ
-- -- -- -- -- -- --     { (n+m , (n' , n'≡n) , (m' , m'=m)) →
-- -- -- -- -- -- --       suc n+m , (suc n , cong suc {!n'≡n!}) , (m , {!!}) }


-- -- -- -- -- -- -- -- module CannotInstantiateMetavariable where
-- -- -- -- -- -- -- --   open import Agda.Primitive
-- -- -- -- -- -- -- --   postulate
-- -- -- -- -- -- -- --     Σ  : (A : Set) (B : A → Set) → Set
-- -- -- -- -- -- -- --     μ₀ : {A : Set} {B : A → Set} → Σ A B → A
-- -- -- -- -- -- -- --     μ₁ : ∀ {A : Set} {B : A → Set} {X : Set} → (X → Σ A B) → X → A

-- -- -- -- -- -- -- --     A : Set
-- -- -- -- -- -- -- --     B : Set
-- -- -- -- -- -- -- --     foo₀ : Σ A λ _ → B

-- -- -- -- -- -- -- --     C : Set
-- -- -- -- -- -- -- --     F : ∀ {C : Set} → C → Set
-- -- -- -- -- -- -- --     foo₁ : (c : C) → Σ A λ _ → F c

-- -- -- -- -- -- -- --   test-μ₀ : A
-- -- -- -- -- -- -- --   test-μ₀ = μ₀ foo₀

-- -- -- -- -- -- -- --   test-μ₁ : C → A
-- -- -- -- -- -- -- --   test-μ₁ c = μ₁ (λ _ → foo₁ c) c

-- -- -- -- -- -- -- -- --   test-μ₁ : ∀ {A C : Set} → (c : C) → A
-- -- -- -- -- -- -- -- --   test-μ₁ = μ₁ foo₁

-- -- -- -- -- -- -- -- -- -- open import Agda.Primitive
-- -- -- -- -- -- -- -- -- -- infixr 1 _,_
-- -- -- -- -- -- -- -- -- -- data Σ' {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
-- -- -- -- -- -- -- -- -- --   _,_ : (x : A) (y : B) → Σ' A B

-- -- -- -- -- -- -- -- -- -- fst' : ∀ {a b} {A : Set a} {B : Set b} → Σ' A B → A
-- -- -- -- -- -- -- -- -- -- fst' (x , y) = x

-- -- -- -- -- -- -- -- -- -- infixr 3 _×'_
-- -- -- -- -- -- -- -- -- -- _×'_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
-- -- -- -- -- -- -- -- -- -- A ×' B = Σ' A B


-- -- -- -- -- -- -- -- -- -- Mem : ∀ {a} {A : Set a} → A → Set a
-- -- -- -- -- -- -- -- -- -- Mem x = Σ _ (_≡ x)

-- -- -- -- -- -- -- -- -- -- μ₀ : ∀ {a b} {A : Set a} {B : Set b} → Σ A (λ _ → B) → A
-- -- -- -- -- -- -- -- -- -- μ₀ = fst

-- -- -- -- -- -- -- -- -- -- μ₂ : ∀ {a b c d} {A : Set a} {B : Set b} → {C : Set c} {D : Set d} → (C → D → A × B) → C → D → A
-- -- -- -- -- -- -- -- -- -- μ₂ = λ f c d → μ₀ (f c d)

-- -- -- -- -- -- -- -- -- -- open import Tactic.Reflection
-- -- -- -- -- -- -- -- -- -- open import Prelude.Nat

-- -- -- -- -- -- -- -- -- -- macro
-- -- -- -- -- -- -- -- -- --   m₂ : Tactic
-- -- -- -- -- -- -- -- -- --   m₂ hole = hole =′ `λ (`λ (def₁ (quote μ₀) (var₂ 2 (var₀ 1) (var₀ 0))))

-- -- -- -- -- -- -- -- -- -- test-μ₂ : {X : Set → Set} {C D : Set} → (F : C → D → Set × X C) → C → D → Set
-- -- -- -- -- -- -- -- -- -- test-μ₂ F = μ₂ F

-- -- -- -- -- -- -- -- -- -- test-2 : ∀ {A B : Set} → ((l : A) → (r : B) → Set × Mem l × Mem r) → (l : A) → (r : B) → Set
-- -- -- -- -- -- -- -- -- -- test-2 = λ x l r → {!!}

-- -- -- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- -- -- --   A : Set
-- -- -- -- -- -- -- -- -- --   M : A → Set
-- -- -- -- -- -- -- -- -- --   m : (l : A) → Set ×' M l
-- -- -- -- -- -- -- -- -- --   n : (l : A) → Set ×' M l ×' M l

-- -- -- -- -- -- -- -- -- -- mreduce : A → Set
-- -- -- -- -- -- -- -- -- -- mreduce = λ x → fst' (m x)

-- -- -- -- -- -- -- -- -- -- mreducer : ((l : A) → Set ×' M l) → (l : A) → Set
-- -- -- -- -- -- -- -- -- -- mreducer x l = fst' (x l)

-- -- -- -- -- -- -- -- -- -- mreducer' : ∀ {b} {B : Set b} → ((l : A) → Set ×' B) → (l : A) → Set
-- -- -- -- -- -- -- -- -- -- mreducer' x l = fst' (x l)

-- -- -- -- -- -- -- -- -- -- test-mreducer : A → Set
-- -- -- -- -- -- -- -- -- -- test-mreducer = mreducer' m


-- -- -- -- -- -- -- -- -- -- -- module UnderstandingCallByName-2 where
-- -- -- -- -- -- -- -- -- -- --   open import Prelude.Nat
-- -- -- -- -- -- -- -- -- -- --   open import Prelude.Product
-- -- -- -- -- -- -- -- -- -- --   open import Prelude.Ord
-- -- -- -- -- -- -- -- -- -- --   open import Prelude.Bool
-- -- -- -- -- -- -- -- -- -- --   open import Prelude

-- -- -- -- -- -- -- -- -- -- --   lem : (n : Nat) → (Nat.suc n ≥? suc n) ≡ true
-- -- -- -- -- -- -- -- -- -- --   lem n with compare (Nat.suc n) (suc n)
-- -- -- -- -- -- -- -- -- -- --   lem n | less (diff k eq) = {!!}
-- -- -- -- -- -- -- -- -- -- --   lem n | equal eq = {!!}
-- -- -- -- -- -- -- -- -- -- --   lem n | greater gt = {!!}

-- -- -- -- -- -- -- -- -- -- --   lem' : (n : Nat) → (Nat.suc n ≥? suc n) ≡ (n ≥? n)
-- -- -- -- -- -- -- -- -- -- --   lem' zero = {!!}
-- -- -- -- -- -- -- -- -- -- --   lem' (suc n) = {!lem' n!}

-- -- -- -- -- -- -- -- -- -- --   lem'' : (n : Nat) → IsTrue (n ≥? suc zero)
-- -- -- -- -- -- -- -- -- -- --   lem'' = {!!}

-- -- -- -- -- -- -- -- -- -- --   &lem : (a b : Bool) → IsTrue a → IsTrue b → IsTrue (a && b)
-- -- -- -- -- -- -- -- -- -- --   &lem false false () x₁
-- -- -- -- -- -- -- -- -- -- --   &lem false true () x₁
-- -- -- -- -- -- -- -- -- -- --   &lem true false true ()
-- -- -- -- -- -- -- -- -- -- --   &lem true true true true = true

-- -- -- -- -- -- -- -- -- -- --   sucn≥?sucn : (n : Nat) → IsTrue (_≥?_ {A = Nat} (suc n) (suc n)) --(Nat.suc n ≥? suc n)
-- -- -- -- -- -- -- -- -- -- --   sucn≥?sucn n = {!n!}

-- -- -- -- -- -- -- -- -- -- --   T : (n : Nat) → Σ Nat λ m → IsTrue (m ≥? n && m ≥? suc zero)
-- -- -- -- -- -- -- -- -- -- --   T zero = suc zero , {!!}
-- -- -- -- -- -- -- -- -- -- --   T (suc n) = suc n , {!snd (T n)!}

-- -- -- -- -- -- -- -- -- -- -- module UnderstandingCallByName where

-- -- -- -- -- -- -- -- -- -- --   data Bool : Set where
-- -- -- -- -- -- -- -- -- -- --     true false : Bool

-- -- -- -- -- -- -- -- -- -- --   data Nat : Set where
-- -- -- -- -- -- -- -- -- -- --     zero : Nat
-- -- -- -- -- -- -- -- -- -- --     suc  : (n : Nat) → Nat

-- -- -- -- -- -- -- -- -- -- --   _<_ : Nat → Nat → Bool
-- -- -- -- -- -- -- -- -- -- --   _     < zero  = false
-- -- -- -- -- -- -- -- -- -- --   zero  < suc _ = true
-- -- -- -- -- -- -- -- -- -- --   suc n < suc m = n < m

-- -- -- -- -- -- -- -- -- -- --   -- S n = minimum of suc zero and n
-- -- -- -- -- -- -- -- -- -- --   S : Nat → Nat
-- -- -- -- -- -- -- -- -- -- --   S n with n < suc zero
-- -- -- -- -- -- -- -- -- -- --   ... | true = suc zero
-- -- -- -- -- -- -- -- -- -- --   ... | false = n

-- -- -- -- -- -- -- -- -- -- --   T : Nat → Nat
-- -- -- -- -- -- -- -- -- -- --   T zero = suc zero
-- -- -- -- -- -- -- -- -- -- --   T (suc n) = (suc n)

-- -- -- -- -- -- -- -- -- -- --   data _≡_ {A : Set} (x : A) : A → Set where
-- -- -- -- -- -- -- -- -- -- --     refl : x ≡ x

-- -- -- -- -- -- -- -- -- -- --   --open import Agda.Builtin.Equality

-- -- -- -- -- -- -- -- -- -- -- --  test-S : S (S (S (S (S (suc zero))))) ≡ suc zero
-- -- -- -- -- -- -- -- -- -- -- --  test-S = refl
-- -- -- -- -- -- -- -- -- -- -- --  test-S : S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (suc zero)))))))))))))))))))))))))))))))))))))))))) ≡ suc zero
-- -- -- -- -- -- -- -- -- -- -- --  test-S = {!refl!}

-- -- -- -- -- -- -- -- -- -- --   test-T : T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (suc zero)))))))))))))))))))))))))))))))))))))))))) ≡ suc zero
-- -- -- -- -- -- -- -- -- -- --   test-T = refl

-- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero)))
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | S (S (suc zero)) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | S (S (suc zero) | S (suc zero) < suc zero) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | S (S (suc zero) | (S (suc zero) | suc zero < suc zero) < suc zero) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | S (S (suc zero) | (S (suc zero) | suc zero < suc zero | zero < zero) < suc zero) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | S (S (suc zero) | (S (suc zero) | suc zero < suc zero | false) < suc zero) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | S (S (suc zero) | (S (suc zero) | false) < suc zero) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | S (S (suc zero) | suc zero < suc zero) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | S (S (suc zero) | suc zero < suc zero | zero < zero) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | S (S (suc zero) | suc zero < suc zero | false) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | S (S (suc zero) | false) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | S (suc zero) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | (S (suc zero) | suc zero < suc zero) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | (S (suc zero) | suc zero < suc zero | zero < zero) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | (S (suc zero) | suc zero < suc zero | false) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | (S (suc zero) | false) < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | suc zero < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | suc zero < suc zero | zero < zero
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | suc zero < suc zero | false
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero))) | false
-- -- -- -- -- -- -- -- -- -- -- S (S (suc zero))


-- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero)))
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero) | suc zero < suc zero))
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero) | suc zero < suc zero | zero < zero))
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero) | suc zero < suc zero | false))
-- -- -- -- -- -- -- -- -- -- -- S (S (S (suc zero) | false))
-- -- -- -- -- -- -- -- -- -- -- S (S (suc zero))
-- -- -- -- -- -- -- -- -- -- -- S (S (suc zero) | suc zero < suc zero)
-- -- -- -- -- -- -- -- -- -- -- S (S (suc zero) | suc zero < suc zero | zero < zero)
-- -- -- -- -- -- -- -- -- -- -- S (S (suc zero) | suc zero < suc zero | false)
-- -- -- -- -- -- -- -- -- -- -- S (S (suc zero) | false)
-- -- -- -- -- -- -- -- -- -- -- S (suc zero)
-- -- -- -- -- -- -- -- -- -- -- S (suc zero) | suc zero < suc zero
-- -- -- -- -- -- -- -- -- -- -- S (suc zero) | suc zero < suc zero | zero < zero
-- -- -- -- -- -- -- -- -- -- -- S (suc zero) | suc zero < suc zero | false
-- -- -- -- -- -- -- -- -- -- -- S (suc zero) | false
-- -- -- -- -- -- -- -- -- -- -- S (suc zero) | false
-- -- -- -- -- -- -- -- -- -- -- -}


-- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- module CallMacroFromMacro-2238 where
-- -- -- -- -- -- -- -- -- -- -- --   open import Agda.Builtin.Reflection
-- -- -- -- -- -- -- -- -- -- -- --   open import Agda.Builtin.Unit
-- -- -- -- -- -- -- -- -- -- -- --   open import Agda.Builtin.List

-- -- -- -- -- -- -- -- -- -- -- --   infixl 6 _>>=_
-- -- -- -- -- -- -- -- -- -- -- --   _>>=_ = bindTC

-- -- -- -- -- -- -- -- -- -- -- --   pattern rArg v x = arg (arg-info v relevant) x
-- -- -- -- -- -- -- -- -- -- -- --   pattern vArg x = rArg visible x

-- -- -- -- -- -- -- -- -- -- -- --   macro
-- -- -- -- -- -- -- -- -- -- -- --     callee : Name → Term → TC ⊤
-- -- -- -- -- -- -- -- -- -- -- --     callee n hole = unify hole (def n [])

-- -- -- -- -- -- -- -- -- -- -- --     caller : Name → Term → TC ⊤
-- -- -- -- -- -- -- -- -- -- -- --     caller n hole = quoteTC n >>= λ n' → unify hole (def (quote callee) (vArg n' ∷ vArg hole ∷ []))

-- -- -- -- -- -- -- -- -- -- -- --   fee : ⊤
-- -- -- -- -- -- -- -- -- -- -- --   fee = tt

-- -- -- -- -- -- -- -- -- -- -- --   foo : ⊤
-- -- -- -- -- -- -- -- -- -- -- --   foo = caller fee
-- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- module FindTheMeta where
-- -- -- -- -- -- -- -- -- -- -- --   case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
-- -- -- -- -- -- -- -- -- -- -- --   case x of f = f x

-- -- -- -- -- -- -- -- -- -- -- -- --  macro
-- -- -- -- -- -- -- -- -- -- -- -- --    showit : Name → Tactic
-- -- -- -- -- -- -- -- -- -- -- -- --    showit n hole = getDefinition n >>= quoteTC >>= λ d → unify hole d

-- -- -- -- -- -- -- -- -- -- -- -- module ShowDefinitions-MetaProblem where

-- -- -- -- -- -- -- -- -- -- -- --   open import Agda.Builtin.Reflection
-- -- -- -- -- -- -- -- -- -- -- --   open import Agda.Builtin.List

-- -- -- -- -- -- -- -- -- -- -- --   case_of_ : {A : Set} {B : Set} → A → (A → B) → B
-- -- -- -- -- -- -- -- -- -- -- --   case x of f = f x

-- -- -- -- -- -- -- -- -- -- -- --   record R₁ : Set where
-- -- -- -- -- -- -- -- -- -- -- --     constructor C

-- -- -- -- -- -- -- -- -- -- -- --   record R₂ : Set where
-- -- -- -- -- -- -- -- -- -- -- --     constructor C

-- -- -- -- -- -- -- -- -- -- -- --   infixl 1 _>>=_
-- -- -- -- -- -- -- -- -- -- -- --   _>>=_ = bindTC

-- -- -- -- -- -- -- -- -- -- -- --   foo : R₂ → R₂
-- -- -- -- -- -- -- -- -- -- -- --   foo n = case n of λ {C → C}

-- -- -- -- -- -- -- -- -- -- -- --   macro
-- -- -- -- -- -- -- -- -- -- -- --     show : Name → Term → TC _
-- -- -- -- -- -- -- -- -- -- -- --     show n hole = getDefinition n >>= quoteTC >>= λ d → unify hole d

-- -- -- -- -- -- -- -- -- -- -- --   test-area : Term
-- -- -- -- -- -- -- -- -- -- -- --   test-area = {!show foo!}

-- -- -- -- -- -- -- -- -- -- -- -- module ShowDefinitions where
-- -- -- -- -- -- -- -- -- -- -- --   open import Prelude
-- -- -- -- -- -- -- -- -- -- -- --   open import Tactic.Reflection

-- -- -- -- -- -- -- -- -- -- -- --   record Sum' : Set where
-- -- -- -- -- -- -- -- -- -- -- --     constructor _,_
-- -- -- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- -- -- --       A B : Nat

-- -- -- -- -- -- -- -- -- -- -- --   tester-let : Sum' → Sum'
-- -- -- -- -- -- -- -- -- -- -- --   tester-let nm = let n , m = nm in m , n

-- -- -- -- -- -- -- -- -- -- -- --   tester-lhs : Sum' → Sum'
-- -- -- -- -- -- -- -- -- -- -- --   tester-lhs (n , m) = m , n

-- -- -- -- -- -- -- -- -- -- -- --   tester-with : Sum' → Sum'
-- -- -- -- -- -- -- -- -- -- -- --   tester-with nm with nm
-- -- -- -- -- -- -- -- -- -- -- --   ... | n , m = m , n

-- -- -- -- -- -- -- -- -- -- -- --   tester-case-of : Sum' → Sum'
-- -- -- -- -- -- -- -- -- -- -- --   tester-case-of nm = case nm of λ { (n , m) → m , n }

-- -- -- -- -- -- -- -- -- -- -- --   record Sum'' : Set where
-- -- -- -- -- -- -- -- -- -- -- --     constructor _,_
-- -- -- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- -- -- --       A : Nat
-- -- -- -- -- -- -- -- -- -- -- --       B : Nat

-- -- -- -- -- -- -- -- -- -- -- --   tester-case-of' : Sum'' → Sum''
-- -- -- -- -- -- -- -- -- -- -- --   tester-case-of' n = case_of_ {lzero} {lzero} {Sum''} {Sum''} n λ { (m , l) → (m , l) }

-- -- -- -- -- -- -- -- -- -- -- --   tester-lambda : Sum' → Sum'
-- -- -- -- -- -- -- -- -- -- -- --   tester-lambda = λ { (n , m) → m , n }

-- -- -- -- -- -- -- -- -- -- -- --   open import Tactic.Reflection.Quote
-- -- -- -- -- -- -- -- -- -- -- --   open import Container.Traversable

-- -- -- -- -- -- -- -- -- -- -- --   {- List (Arg Type)
-- -- -- -- -- -- -- -- -- -- -- --         traverse : ∀ {F : Set a → Set a} {A B} {{AppF : Applicative F}} → (A → F B) → T A → F (T B)
-- -- -- -- -- -- -- -- -- -- -- --   -}

-- -- -- -- -- -- -- -- -- -- -- --   {-# TERMINATING #-}
-- -- -- -- -- -- -- -- -- -- -- --   blockOnMeat : Term → TC Term
-- -- -- -- -- -- -- -- -- -- -- --   blockOnMeat (var x args) = var x <$> (traverse ∘ traverse) blockOnMeat args
-- -- -- -- -- -- -- -- -- -- -- --   blockOnMeat (con c args) = con c <$> (traverse ∘ traverse) blockOnMeat args
-- -- -- -- -- -- -- -- -- -- -- --   blockOnMeat (def f args) = extendContext (arg (arg-info visible relevant) (var (fromNat 0) [])) (normalise (def f args)) -- def f <$> (traverse ∘ traverse) blockOnMeat args
-- -- -- -- -- -- -- -- -- -- -- --   blockOnMeat (lam v t) = lam v <$> traverse blockOnMeat t
-- -- -- -- -- -- -- -- -- -- -- --   blockOnMeat (pat-lam cs args) = normalise (pat-lam cs args) -- pat-lam cs <$> (traverse ∘ traverse) blockOnMeat args -- TODO Clause
-- -- -- -- -- -- -- -- -- -- -- --   blockOnMeat (pi a b) = pi <$> traverse blockOnMeat a <*> traverse blockOnMeat b
-- -- -- -- -- -- -- -- -- -- -- --   blockOnMeat (agda-sort s) = pure (agda-sort s) -- TODO Sort
-- -- -- -- -- -- -- -- -- -- -- --   blockOnMeat (lit l) = pure (lit l)
-- -- -- -- -- -- -- -- -- -- -- --   blockOnMeat (meta x x₁) = blockOnMeta! x
-- -- -- -- -- -- -- -- -- -- -- --   blockOnMeat unknown = pure unknown

-- -- -- -- -- -- -- -- -- -- -- --   macro
-- -- -- -- -- -- -- -- -- -- -- --     showit : Name → Tactic
-- -- -- -- -- -- -- -- -- -- -- --     showit n hole = getDefinition n >>= quoteTC >>= λ d → unify hole d

-- -- -- -- -- -- -- -- -- -- -- --     showwith : Name → Tactic
-- -- -- -- -- -- -- -- -- -- -- --     showwith n hole = getDefinition n >>= helper where
-- -- -- -- -- -- -- -- -- -- -- --       helper : Definition → TC ⊤
-- -- -- -- -- -- -- -- -- -- -- --       helper (function (clause _ (def w _) ∷ [])) = getDefinition w >>= quoteTC >>= λ d → unify hole d
-- -- -- -- -- -- -- -- -- -- -- --       helper _ = return _

-- -- -- -- -- -- -- -- -- -- -- --     destruct-case-of : Tactic
-- -- -- -- -- -- -- -- -- -- -- --     destruct-case-of hole = do
-- -- -- -- -- -- -- -- -- -- -- --       d ← getDefinition (quote tester-case-of) -|
-- -- -- -- -- -- -- -- -- -- -- --       case d of λ
-- -- -- -- -- -- -- -- -- -- -- -- --      { (function (clause _ (def _ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ (arg _ pl) ∷ _)) ∷ _)) → blockOnMeat pl >>= quoteTC >>= unify hole
-- -- -- -- -- -- -- -- -- -- -- --       { (function (clause _ pl ∷ _)) → quoteTC pl >>= unify hole
-- -- -- -- -- -- -- -- -- -- -- --       ; _ → pure _
-- -- -- -- -- -- -- -- -- -- -- --       }

-- -- -- -- -- -- -- -- -- -- -- --   shower : Term
-- -- -- -- -- -- -- -- -- -- -- --   shower = {!showit tester-case-of'!}
-- -- -- -- -- -- -- -- -- -- -- --   -- showit tester-case-of'
-- -- -- -- -- -- -- -- -- -- -- --   -- destruct-case-of

-- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- pat-lam
-- -- -- -- -- -- -- -- -- -- -- -- (clause
-- -- -- -- -- -- -- -- -- -- -- --  (arg (arg-info visible relevant)
-- -- -- -- -- -- -- -- -- -- -- --   (con (quote Sum'._,_)
-- -- -- -- -- -- -- -- -- -- -- --    (arg (arg-info visible relevant) (var "n") ∷
-- -- -- -- -- -- -- -- -- -- -- --     arg (arg-info visible relevant) (var "m") ∷ []))
-- -- -- -- -- -- -- -- -- -- -- --   ∷ [])
-- -- -- -- -- -- -- -- -- -- -- --  (meta _15
-- -- -- -- -- -- -- -- -- -- -- --   (arg (arg-info visible relevant) (var 2 []) ∷
-- -- -- -- -- -- -- -- -- -- -- --    arg (arg-info visible relevant) (var 1 []) ∷
-- -- -- -- -- -- -- -- -- -- -- --    arg (arg-info visible relevant) (var 0 []) ∷ []))
-- -- -- -- -- -- -- -- -- -- -- --  ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -}


-- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- tester-lambda
-- -- -- -- -- -- -- -- -- -- -- -- function
-- -- -- -- -- -- -- -- -- -- -- -- (clause []
-- -- -- -- -- -- -- -- -- -- -- --  (pat-lam
-- -- -- -- -- -- -- -- -- -- -- --   (clause
-- -- -- -- -- -- -- -- -- -- -- --    (arg (arg-info visible relevant)
-- -- -- -- -- -- -- -- -- -- -- --     (con (quote Sum'._,_)
-- -- -- -- -- -- -- -- -- -- -- --      (arg (arg-info visible relevant) (var "n") ∷
-- -- -- -- -- -- -- -- -- -- -- --       arg (arg-info visible relevant) (var "m") ∷ []))
-- -- -- -- -- -- -- -- -- -- -- --     ∷ [])
-- -- -- -- -- -- -- -- -- -- -- --    (con (quote Sum'._,_)
-- -- -- -- -- -- -- -- -- -- -- --     (arg (arg-info visible relevant) (var 0 []) ∷
-- -- -- -- -- -- -- -- -- -- -- --      arg (arg-info visible relevant) (var 1 []) ∷ []))
-- -- -- -- -- -- -- -- -- -- -- --    ∷ [])
-- -- -- -- -- -- -- -- -- -- -- --   [])
-- -- -- -- -- -- -- -- -- -- -- --  ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- tester-case-of
-- -- -- -- -- -- -- -- -- -- -- -- function
-- -- -- -- -- -- -- -- -- -- -- -- (clause (arg (arg-info visible relevant) (var "nm") ∷ [])
-- -- -- -- -- -- -- -- -- -- -- --  (def (quote case_of_)
-- -- -- -- -- -- -- -- -- -- -- --   (arg (arg-info hidden relevant) (def (quote lzero) []) ∷
-- -- -- -- -- -- -- -- -- -- -- --    arg (arg-info hidden relevant) (def (quote lzero) []) ∷
-- -- -- -- -- -- -- -- -- -- -- --    arg (arg-info hidden relevant) (def (quote Sum') []) ∷
-- -- -- -- -- -- -- -- -- -- -- --    arg (arg-info hidden relevant) (def (quote Sum') []) ∷
-- -- -- -- -- -- -- -- -- -- -- --    arg (arg-info visible relevant) (var 0 []) ∷
-- -- -- -- -- -- -- -- -- -- -- --    arg (arg-info visible relevant)
-- -- -- -- -- -- -- -- -- -- -- --    (pat-lam
-- -- -- -- -- -- -- -- -- -- -- --       (clause
-- -- -- -- -- -- -- -- -- -- -- --          (arg (arg-info visible relevant)
-- -- -- -- -- -- -- -- -- -- -- --              (con (quote Sum'._,_)
-- -- -- -- -- -- -- -- -- -- -- --               (arg (arg-info visible relevant) (var "n") ∷
-- -- -- -- -- -- -- -- -- -- -- --                arg (arg-info visible relevant) (var "m") ∷ []))
-- -- -- -- -- -- -- -- -- -- -- --              ∷ []
-- -- -- -- -- -- -- -- -- -- -- --          )
-- -- -- -- -- -- -- -- -- -- -- --          (meta _15
-- -- -- -- -- -- -- -- -- -- -- --           (arg (arg-info visible relevant) (var 2 []) ∷
-- -- -- -- -- -- -- -- -- -- -- --            arg (arg-info visible relevant) (var 1 []) ∷
-- -- -- -- -- -- -- -- -- -- -- --            arg (arg-info visible relevant) (var 0 []) ∷ []))
-- -- -- -- -- -- -- -- -- -- -- --        ∷ []
-- -- -- -- -- -- -- -- -- -- -- --       )
-- -- -- -- -- -- -- -- -- -- -- --       (arg (arg-info visible relevant) (var 0 []) ∷ [])
-- -- -- -- -- -- -- -- -- -- -- --    )
-- -- -- -- -- -- -- -- -- -- -- --    ∷ []))
-- -- -- -- -- -- -- -- -- -- -- --  ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- tester-let
-- -- -- -- -- -- -- -- -- -- -- -- function
-- -- -- -- -- -- -- -- -- -- -- -- (clause (arg (arg-info visible relevant) (var "nm") ∷ [])
-- -- -- -- -- -- -- -- -- -- -- --  (con (quote Sum'._,_)
-- -- -- -- -- -- -- -- -- -- -- --   (arg (arg-info visible relevant)
-- -- -- -- -- -- -- -- -- -- -- --    (def (quote Sum'.B)
-- -- -- -- -- -- -- -- -- -- -- --     (arg (arg-info visible relevant) (var 0 []) ∷ []))
-- -- -- -- -- -- -- -- -- -- -- --    ∷
-- -- -- -- -- -- -- -- -- -- -- --    arg (arg-info visible relevant)
-- -- -- -- -- -- -- -- -- -- -- --    (def (quote Sum'.A)
-- -- -- -- -- -- -- -- -- -- -- --     (arg (arg-info visible relevant) (var 0 []) ∷ []))
-- -- -- -- -- -- -- -- -- -- -- --    ∷ []))
-- -- -- -- -- -- -- -- -- -- -- --  ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- tester-lhs
-- -- -- -- -- -- -- -- -- -- -- -- function
-- -- -- -- -- -- -- -- -- -- -- -- (clause
-- -- -- -- -- -- -- -- -- -- -- --  (arg (arg-info visible relevant)
-- -- -- -- -- -- -- -- -- -- -- --   (con (quote Sum'._,_)
-- -- -- -- -- -- -- -- -- -- -- --    (arg (arg-info visible relevant) (var "n") ∷
-- -- -- -- -- -- -- -- -- -- -- --     arg (arg-info visible relevant) (var "m") ∷ []))
-- -- -- -- -- -- -- -- -- -- -- --   ∷ [])
-- -- -- -- -- -- -- -- -- -- -- --  (con (quote Sum'._,_)
-- -- -- -- -- -- -- -- -- -- -- --   (arg (arg-info visible relevant) (var 0 []) ∷
-- -- -- -- -- -- -- -- -- -- -- --    arg (arg-info visible relevant) (var 1 []) ∷ []))
-- -- -- -- -- -- -- -- -- -- -- --  ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- showwith tester-with
-- -- -- -- -- -- -- -- -- -- -- -- function
-- -- -- -- -- -- -- -- -- -- -- -- (clause
-- -- -- -- -- -- -- -- -- -- -- --  (arg (arg-info visible relevant) (var "nm") ∷
-- -- -- -- -- -- -- -- -- -- -- --   arg (arg-info visible relevant)
-- -- -- -- -- -- -- -- -- -- -- --   (con (quote Sum'._,_)
-- -- -- -- -- -- -- -- -- -- -- --    (arg (arg-info visible relevant) (var "n") ∷
-- -- -- -- -- -- -- -- -- -- -- --     arg (arg-info visible relevant) (var "m") ∷ []))
-- -- -- -- -- -- -- -- -- -- -- --   ∷ [])
-- -- -- -- -- -- -- -- -- -- -- --  (con (quote Sum'._,_)
-- -- -- -- -- -- -- -- -- -- -- --   (arg (arg-info visible relevant) (var 0 []) ∷
-- -- -- -- -- -- -- -- -- -- -- --    arg (arg-info visible relevant) (var 1 []) ∷ []))
-- -- -- -- -- -- -- -- -- -- -- --  ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- module PreludeBool where
-- -- -- -- -- -- -- -- -- -- -- -- --   data ⊥ : Set where

-- -- -- -- -- -- -- -- -- -- -- -- --   infix 4 ¬_
-- -- -- -- -- -- -- -- -- -- -- -- --   ¬_ : ∀ {a} (A : Set a) → Set a
-- -- -- -- -- -- -- -- -- -- -- -- --   ¬ A = A → ⊥

-- -- -- -- -- -- -- -- -- -- -- -- --   data Dec {a} (P : Set a) : Set a where
-- -- -- -- -- -- -- -- -- -- -- -- --     yes : P → Dec P
-- -- -- -- -- -- -- -- -- -- -- -- --     no  : ¬ P → Dec P

-- -- -- -- -- -- -- -- -- -- -- -- --   open import Agda.Builtin.Equality

-- -- -- -- -- -- -- -- -- -- -- -- --   record Eq {a} (A : Set a) : Set a where
-- -- -- -- -- -- -- -- -- -- -- -- --     infix 4 _==_
-- -- -- -- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- -- -- -- --       _==_ : (x y : A) → Dec (x ≡ y)

-- -- -- -- -- -- -- -- -- -- -- -- --   open Eq {{...}}

-- -- -- -- -- -- -- -- -- -- -- -- --   open import Agda.Builtin.Bool

-- -- -- -- -- -- -- -- -- -- -- -- --   instance
-- -- -- -- -- -- -- -- -- -- -- -- --     EqBool : Eq Bool
-- -- -- -- -- -- -- -- -- -- -- -- --     _==_ {{EqBool}} false false = yes refl
-- -- -- -- -- -- -- -- -- -- -- -- --     _==_ {{EqBool}} false true  = no λ ()
-- -- -- -- -- -- -- -- -- -- -- -- --     _==_ {{EqBool}} true  false = no λ ()
-- -- -- -- -- -- -- -- -- -- -- -- --     _==_ {{EqBool}} true  true  = yes refl


-- -- -- -- -- -- -- -- -- -- -- -- -- -- module PreludeBool where

-- -- -- -- -- -- -- -- -- -- -- -- -- --   --open import Prelude.Unit
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --open import Prelude.Empty
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --open import Prelude.Equality
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --open import Prelude.Decidable
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --open import Prelude.Function

-- -- -- -- -- -- -- -- -- -- -- -- -- --   data ⊥ : Set where

-- -- -- -- -- -- -- -- -- -- -- -- -- --   infix 4 ¬_
-- -- -- -- -- -- -- -- -- -- -- -- -- --   ¬_ : ∀ {a} (A : Set a) → Set a
-- -- -- -- -- -- -- -- -- -- -- -- -- --   ¬ A = A → ⊥

-- -- -- -- -- -- -- -- -- -- -- -- -- --   data Dec {a} (P : Set a) : Set a where
-- -- -- -- -- -- -- -- -- -- -- -- -- --     yes : P → Dec P
-- -- -- -- -- -- -- -- -- -- -- -- -- --     no  : ¬ P → Dec P

-- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Agda.Builtin.Equality public

-- -- -- -- -- -- -- -- -- -- -- -- -- --   record Eq {a} (A : Set a) : Set a where
-- -- -- -- -- -- -- -- -- -- -- -- -- --     infix 4 _==_
-- -- -- -- -- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- -- -- -- -- --       _==_ : (x y : A) → Dec (x ≡ y)

-- -- -- -- -- -- -- -- -- -- -- -- -- --   open Eq {{...}} public

-- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Agda.Builtin.Bool public
-- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- --   infix 0 if_then_else_
-- -- -- -- -- -- -- -- -- -- -- -- -- --   if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
-- -- -- -- -- -- -- -- -- -- -- -- -- --   if true  then x else y = x
-- -- -- -- -- -- -- -- -- -- -- -- -- --   if false then x else y = y
-- -- -- -- -- -- -- -- -- -- -- -- -- --   {-# INLINE if_then_else_ #-}

-- -- -- -- -- -- -- -- -- -- -- -- -- --   infixr 3 _&&_
-- -- -- -- -- -- -- -- -- -- -- -- -- --   infixr 2 _||_

-- -- -- -- -- -- -- -- -- -- -- -- -- --   _||_ : Bool → Bool → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- --   true  || _ = true
-- -- -- -- -- -- -- -- -- -- -- -- -- --   false || x = x
-- -- -- -- -- -- -- -- -- -- -- -- -- --   {-# INLINE _||_ #-}

-- -- -- -- -- -- -- -- -- -- -- -- -- --   _&&_ : Bool → Bool → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- --   true  && x = x
-- -- -- -- -- -- -- -- -- -- -- -- -- --   false && _ = false
-- -- -- -- -- -- -- -- -- -- -- -- -- --   {-# INLINE _&&_ #-}

-- -- -- -- -- -- -- -- -- -- -- -- -- --   not : Bool → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- --   not true  = false
-- -- -- -- -- -- -- -- -- -- -- -- -- --   not false = true
-- -- -- -- -- -- -- -- -- -- -- -- -- --   {-# INLINE not #-}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- --   data IsTrue : Bool → Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- --     instance true : IsTrue true

-- -- -- -- -- -- -- -- -- -- -- -- -- --   data IsFalse : Bool → Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- --     instance false : IsFalse false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   instance
-- -- -- -- -- -- -- -- -- -- -- -- -- --     EqBool : Eq Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- --     _==_ {{EqBool}} false false = yes refl
-- -- -- -- -- -- -- -- -- -- -- -- -- --     _==_ {{EqBool}} false true  = no λ ()
-- -- -- -- -- -- -- -- -- -- -- -- -- --     _==_ {{EqBool}} true  false = no λ ()
-- -- -- -- -- -- -- -- -- -- -- -- -- --     _==_ {{EqBool}} true  true  = yes refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   decBool : ∀ b → Dec (IsTrue b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   decBool false = no λ ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   decBool true  = yes true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {-# INLINE decBool #-}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isYes : ∀ {a} {A : Set a} → Dec A → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isYes (yes _) = true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isYes (no _)  = false

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isNo : ∀ {a} {A : Set a} → Dec A → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isNo = not ∘ isYes

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   infix 0 if′_then_else_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   if′_then_else_ : ∀ {a} {A : Set a} (b : Bool) → ({{_ : IsTrue b}} → A) → ({{_ : IsFalse b}} → A) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   if′ true  then x else _ = x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   if′ false then _ else y = y


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --module Prelude where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open import Prelude.Bool

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module Maybes where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Prelude

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   postulate
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     P : Set
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     search : Maybe P

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   unMaybe : ∀ {a} {A : Set a} (m : Maybe A) {_ : IsJust m} -> A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   unMaybe nothing {}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   unMaybe (just x) {_} = x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   proof : P
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   proof = unMaybe search

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module Issue1555 where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Agda.Builtin.Unit

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test : {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     : ⊤} → ⊤ → ⊤
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test tt = tt
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module ContentedList where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Prelude

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   data CList {a} (A : Set a) : List A → Set a where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     []  : CList A []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _∷_ : (x : A) {ls : List A} (xs : CList A ls) → CList A (x ∷ ls)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   csingleton : {a : Level} {A : Set a} (x : A) → CList A (x ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   csingleton x = x ∷ []

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   chead : {a : Level} {A : Set a} {x : A} {ls : List A} → CList A (x ∷ ls) → Σ A λ x' → x' ≡ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   chead (x ∷ _) = x , refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module StandardLibrary where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Everything

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module No-eta-equality₁ where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Prelude.Equality

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Σ (A : Set) (B : A -> Set) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      no-eta-equality
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      constructor _,_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        fst : A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        snd : B fst

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Σ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fail : ∀ {A : Set}{B : A -> Set} → (x : Σ A B) → x ≡ (fst x , snd x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fail x = {!refl!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- x != fst x , snd x of type Σ .A .B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- when checking that the expression refl has type x ≡ (fst x , snd x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module No-eta-equality₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Agda.Builtin.Equality

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Pair-η= (A B : Set) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     constructor _,_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       fst : A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       snd : B

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-η= : ∀ {A B : Set} → (p : Pair-η= A B) → Pair-η=.fst p , Pair-η=.snd p ≡ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-η= p = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Pair-η≠ (A B : Set) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     no-eta-equality
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     constructor _,_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       fst : A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       snd : B

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-η≠ : ∀ {A B : Set} → (p : Pair-η≠ A B) → Pair-η≠.fst p , Pair-η≠.snd p ≡ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-η≠ p = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test₂-η≠ : ∀ {A B : Set} → (a : A) (b : B) → (Pair-η≠._,_ a b) ≡ (a , b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test₂-η≠ a b = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   data Pair-data (A B : Set) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _,_ : A → B → Pair-data A B

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst : ∀ {A B : Set} → Pair-data A B → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (a , b) = a

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   snd : ∀ {A B : Set} → Pair-data A B → B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   snd (a , b) = b

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-data : ∀ {A B : Set} → (p : Pair-data A B) → fst p , snd p ≡ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-data p = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module Test-Permutation where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --open import Data.Vec
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --open import Relation.Binary
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Data.Permutation
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Data.Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Data.Nat

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fin : Fin 3
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fin = # 1

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   perm : Permutation 1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   perm = fromℕ 0 ∷ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module ShowExtendedLambda where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Prelude

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   data D : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     d₀ : D
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     d₁ : Nat → D
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     d₂ : String → Nat → D → D

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   example-of-patlam : D → D
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   example-of-patlam d₀ = d₁ 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   example-of-patlam (d₁ n) = d₀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   example-of-patlam (d₂ s n d) = case d of λ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     { d₀ → d₁ 1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ; (d₁ x) → d₁ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ; (d₂ s n d) → d₁ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Tactic.Reflection
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Tactic.Reflection.Quote

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   macro
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     showDef : Name → Tactic
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     showDef n hole = do
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       cs ← getClauses n -|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       typeError [ termErr (` cs) ]

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   data C : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     c : C

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   foo : Set
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   foo = {!showDef example-of-patlam!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module CannotInstantiateMetavariable where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Prelude using (∃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   postulate
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     M : Set → Set
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     bind : ∀ {𝑨 𝑩 : Set} → M 𝑨 → (𝑨 → M 𝑩) → M 𝑩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     bind' : ∀ {𝑨 : Set} {𝑩 : 𝑨 → Set} → M 𝑨 → ((a : 𝑨) → M (𝑩 a)) → ∃ λ a → M (𝑩 a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     A : Set
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     B : A → Set
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     action : (a : A) → M (B a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     MA : M A

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   foo : ∃ λ α → M (B α)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   foo = --bind {A} {{!!}} MA {!action!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         bind' {A} {B} MA action
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Cannot instantiate the metavariable _53 to solution (B a) since it
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   contains the variable a which is not in scope of the metavariable
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   or irrelevant in the metavariable but relevant in the solution
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   when checking that the expression action has type A → M ?1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module UnsolvedMetas where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Prelude
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   postulate
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     M : Set → Set
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     instance
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       MonadM : Monad M
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       FunctorM : Functor M
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     A : Set
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     B : A → Set
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     action : (a : A) → M (B a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     mask : ∀ {a : A} → B a → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     MA : M A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     c : A

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   foo : M (A × A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   foo = MA >>= λ ma → action ma >>= λ b → return (mask b , c)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   data Masked : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     mask' : ∀ {a : A} → B a → Masked

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   bar : M _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   bar = do
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ma ← MA -|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     b ← action ma -|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     b' ← mask' <$> action ma -|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     return (b' , mask' b , c)
