module AgdaIssue2189 where
  -- produces weird conflict with 𝑽
  module M₁ where
    open import Postlude
    open import Tactic.Reflection.Reright

    open import Tactic.Reflection.Quote
    open import Builtin.Reflection

    macro
      showContext : Tactic
      showContext hole =
        Γ ← getContext -|
        typeError [ termErr (` Γ) ]


    module M₁' {𝑲 𝑽} (let 𝑲𝑽 = 𝑲 ⊔ₗ 𝑽 ; 𝑲𝑽₁ = sucₗ 𝑲𝑽) where
      record R
               {K : Set 𝑲}
               (V : K → Set 𝑽)
               (Carrier : ℕ → Set 𝑲𝑽) (isDecEquivalence/K : Eq K) : Set 𝑲𝑽₁ where
        field
          _∈_ : ∀ {s} → K → Carrier s → Set 𝑲𝑽
          get : ∀ {k : K} {s} {m : Carrier s} → k ∈ m → V k

        infixl 40 _⊆_
        _⊆_ : ∀ {s₁ s₀} → Carrier s₁ → Carrier s₀ → Set 𝑲𝑽
        _⊆_ m₁ m₀ = ∀ {𝑘} → (𝑘∈m₁ : 𝑘 ∈ m₁) → ∃ λ (𝑘∈m₀ : 𝑘 ∈ m₀) → get 𝑘∈m₁ ≡ get 𝑘∈m₀

        field
          choose : ∀ {s} → (m : Carrier s) → Dec (∃ λ k → k ∈ m)

        err₁ : ∀ {s/x} (x : Carrier s/x) → ∃ λ s/z → ∃ λ (z : Carrier s/z) → (x ⊆ z)
        err₁ x with choose x
        err₁ x | yes (a , a∈x) =
          {!!} ,
          {!!} ,
          (λ {𝑘} ∈x → case _≟_ {{isDecEquivalence/K}} 𝑘 a of
            (λ {
              (yes 𝑘≡a) → {!showContext!} -- reright 𝑘≡a {!!}
            ; (no 𝑘≢a) → {!!}
            }))
        err₁ x | no ∉x = {!!}

        err₂ : K → K → Set
        err₂ k a = case _≟_ {{isDecEquivalence/K}} k a of ((λ {
              (yes 𝑘≡a) → {!!} -- reright 𝑘≡a {!!}
            ; (no 𝑘≢a) → {!!}
            }))

  -- error defining helper function
  module M₂ where
    open import Postlude

    module M₂' (𝑲 : Level) where
      open import Tactic.Reflection.Reright

      record R {K : Set 𝑲} (isDecEquivalence/K : Eq K) : Set where
        err₂ : K → K → Set
        err₂ k a = case _≟_ {{isDecEquivalence/K}} k a of ((λ {
              (yes 𝑘≡a) → {!!} -- reright 𝑘≡a {!!}
            ; (no 𝑘≢a) → {!!}
            }))

        err₃ : (k a : K) (k≡a : k ≡ a) → Set
        err₃ k a k≡a = {!!} -- reright k≡a {!!}

  -- ok
  module M₃ where
    open import Postlude
    open import Tactic.Reflection.Reright

    record R {K : Set} (isDecEquivalence/K : Eq K) : Set where
      err₂ : K → K → Set
      err₂ k a = case _≟_ {{isDecEquivalence/K}} k a of ((λ {
            (yes 𝑘≡a) → reright 𝑘≡a {!!}
          ; (no 𝑘≢a) → {!!}
          }))

      err₃ : (k a : K) (k≡a : k ≡ a) → Set
      err₃ k a k≡a = reright k≡a {!!}

  -- error defining helper function
  module M₄ (A : Set) where
    open import Postlude
    open import Tactic.Reflection.Reright

    postulate
      trustMe : ∀ {α} {A : Set α} → A

    record R (a : A) : Set where
    {-
      err : (x : A) (x≡x : x ≡ x) → Set
      err _ x≡x =
        -- reright x≡x {!!} where open import Agda.Builtin.Reflection
        -- helper
        {!!}
        where
    -}

      err : Set
      err = {!helper!} where
        open import Builtin.Reflection
        open import Tactic.Reflection
{-
        helper-type : Type
        helper-type =
          pi (arg (arg-info hidden relevant) (agda-sort (lit 0)))
          (abs "_"
           (pi (arg (arg-info hidden relevant) (var 0 []))
            (abs "_"
             (pi (arg (arg-info hidden relevant) (var 1 []))
              (abs "_"
               (pi
                (arg (arg-info visible irrelevant)
                 (def (quote R) (arg (arg-info visible relevant) (var 0 []) ∷ [])))
                (abs "_"
                 (pi (arg (arg-info visible relevant) (var 3 []))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (def (quote _≡_)
                      (arg (arg-info hidden relevant) (def (quote lzero) []) ∷
                       arg (arg-info hidden relevant) (var 4 []) ∷
                       arg (arg-info visible relevant) (var 3 []) ∷
                       arg (arg-info visible relevant) (var 3 []) ∷ [])))
                    {-(abs "_"
                     (pi
                      (arg (arg-info visible relevant)
                       (def (quote _≡_)
                        (arg (arg-info visible relevant) (var 4 []) ∷
                         arg (arg-info visible relevant) (var 1 []) ∷ [])))-}
                      (abs "_"
                       (pi (arg (arg-info visible relevant) (agda-sort (lit 0)))
                        (abs "_" (agda-sort (lit 0))))))))))))))) -- ))
-}
        helper-type : Type
        helper-type =
          pi (arg (arg-info hidden relevant) (agda-sort (lit 0)))
          (abs "_"
           (pi (arg (arg-info hidden relevant) (var 0 []))
            (abs "_"
             (pi
              (arg (arg-info visible irrelevant)
               (def (quote R) (arg (arg-info visible relevant) (var 0 []) ∷ [])))
              (abs "_" (agda-sort (lit 0)))))))

        helper-patterns : List (Arg Pattern)
        helper-patterns =
          arg (arg-info hidden relevant) (var "_") ∷
          arg (arg-info hidden relevant) (var "_") ∷ []

        helper-term : Term
        helper-term = def₀ (quote trustMe)

        macro
          helper : Tactic
          helper hole = do
            n ← freshName "helper" -|
            catchTC (define (vArg n) helper-type [ clause helper-patterns helper-term ])
                    (typeError ( strErr "error defining helper function" ∷ []))
            ~|
            unify hole helper-term

  module M₅ where
    open import Postlude
    open import Tactic.Reflection.Reright

    open import Builtin.Reflection
    macro
      round-trip : Term → Tactic
      round-trip v hole = unify v hole

    module M (A : Set) where
      record R (a : A) : Set where
        data D : Set where

        fail : D → A → Set
        fail d a = round-trip D

  module M₆ where
    open import Prelude
    open import Tactic.Reflection
    open import Tactic.Reflection.Quote

    postulate
      trustMe : ∀ {α} {A : Set α} → A

    macro
      trust-the-doppelganger : Tactic
      trust-the-doppelganger hole = do
        telescope ← reverse <$> getContext -|
        goal ← inferType hole -|
        nameₕ ← freshName "nameₕ" -|
        (let helper-type = (telPi telescope goal)
             helper-patterns = telePat telescope
          in
            catchTC
              (define (vArg nameₕ) (telPi telescope goal) [ clause (telePat telescope) (def₀ (quote trustMe)) ])
              (typeError (strErr "failed defining a function with type" ∷ termErr (telPi telescope goal) ∷
                          strErr "\nhelper-type:" ∷ termErr helper-type ∷
                          strErr "\n`helper-type:" ∷ termErr (` helper-type) ∷
                          strErr "\nhelper-patterns:" ∷ termErr (` helper-patterns) ∷
                          --strErr "\nhelper-term:" ∷ termErr helper-term ∷
                          --strErr "\n`helper-term:" ∷ termErr (` helper-term) ∷
                          []))
        )
          ~|
        unify hole (def nameₕ (teleArgs telescope))

    module _ (A : Set) where
      record R (P : A) : Set where
      --module _ (P : A) where
        fails : Set
        fails = {!!} -- trust-the-doppelganger -- failed defining a function with type {A₁ : Set} {z : A₁} .(r : R z) → Set

  module M₇ (A : Set) where
    open import Postlude
    open import Tactic.Reflection

    postulate
      trustMe : ∀ {α} {A : Set α} → A

    helper-type : Name → Type
    helper-type n =
      pi (arg (arg-info hidden relevant) (agda-sort (lit 0)))
      (abs "_"
       (pi (arg (arg-info hidden relevant) (var 0 []))
        (abs "_"
         (pi
          (arg (arg-info visible irrelevant)
           (def n (arg (arg-info visible relevant) (var 0 []) ∷ [])))
          (abs "_" (agda-sort (lit 0)))))))

    helper-patterns : List (Arg Pattern)
    helper-patterns =
      arg (arg-info hidden relevant) (var "_") ∷
      arg (arg-info hidden relevant) (var "_") ∷ []

    helper-term : Term
    helper-term = def₀ (quote trustMe)

    macro
      helper : Name → Tactic
      helper nam hole = do
        n ← freshName "helper" -|
        catchTC (define (vArg n) (helper-type nam) [ clause helper-patterns helper-term ])
                (typeError ( strErr "error defining helper function" ∷ []))
        ~|
        unify hole helper-term

    record R (a : Set) : Set where
      err : Set
      err = {!!} -- helper (quote R)

  module M₇' (A : Set) where
    open import Postlude
    open import Tactic.Reflection

    postulate
      trustMe : ∀ {α} {A : Set α} → A

    helper-type : Name → Type
    helper-type n =
      pi (arg (arg-info hidden relevant) (agda-sort (lit 0)))
      (abs "_"
       (pi (arg (arg-info hidden relevant) (agda-sort (lit 0)))
        (abs "_"
         (pi
          (arg (arg-info visible irrelevant)
           (def n (arg (arg-info visible relevant) (var 0 []) ∷ [])))
          (abs "_" (agda-sort (lit 0)))))))
    {-
      pi (arg (arg-info hidden relevant) (agda-sort (lit 0)))
      (abs "_"
       (pi (arg (arg-info hidden relevant) (var 0 []))
        (abs "_"
         (pi
          (arg (arg-info visible irrelevant)
           (def n (arg (arg-info visible relevant) (var 0 []) ∷ [])))
          (abs "_" (agda-sort (lit 0)))))))
    -}

    helper-patterns : List (Arg Pattern)
    helper-patterns =
      arg (arg-info hidden relevant) (var "_") ∷
      arg (arg-info hidden relevant) (var "_") ∷ []

    helper-term : Term
    helper-term = def₀ (quote trustMe)

    macro
      helper : Name → Tactic
      helper nam hole = do
        n ← freshName "helper" -|
        catchTC (define (vArg n) (helper-type nam) [ clause helper-patterns helper-term ])
                (typeError ( strErr "error defining helper function" ∷ []))
        ~|
        unify hole helper-term

    record R-succeeds (a : Set) : Set where
      test : Set
      test = helper (quote R-succeeds)

    record R-fails (a : A) : Set where
      test : Set
      test = {!!} -- helper (quote R)
-- see M₉

  module M₈ where
    open import Prelude
    open import Tactic.Reflection

    postulate
      trustMe : ∀ {α} {A : Set α} → A

    macro
      trust-the-doppelganger : Tactic
      trust-the-doppelganger hole = do
        telescope ← reverse <$> getContext -|
        goal ← inferType hole -|
        nameₕ ← freshName "nameₕ" -|
        catchTC
          (define (vArg nameₕ) (telPi telescope goal) [ clause (telePat telescope) (def₀ (quote trustMe)) ])
          (typeError (strErr "failed defining a function with type" ∷ termErr (telPi telescope goal) ∷ []))
          ~|
        unify hole (def nameₕ (teleArgs telescope))

    module NM₀ where
      postulate
        P : Set

      no-param-succeeds : P
      no-param-succeeds = trust-the-doppelganger

    module NM₁ (A : Set) where
      postulate
        P : Set

      inside-M₁-fails : P
      inside-M₁-fails = trust-the-doppelganger -- failed defining a function with type (A₁ : Set) → P A₁

    outside-M₁-succeeds : (A : Set) → NM₁.P A
    outside-M₁-succeeds = trust-the-doppelganger

  module M₉ where
    open import Prelude
    open import Tactic.Reflection
    open import Tactic.Reflection.Quote
    open import Builtin.Reflection

    helper-type : Name → Type → Type
    helper-type record-name record-parameter-type =
      pi (arg (arg-info hidden relevant) (agda-sort (lit 0)))
      (abs "_"
       (pi (arg (arg-info hidden relevant) record-parameter-type)
        (abs "_"
         (pi
          (arg (arg-info visible irrelevant)
           (def record-name (arg (arg-info visible relevant) (var 0 []) ∷ [])))
          (abs "_" (agda-sort (lit 0)))))))

    helper-patterns : List (Arg Pattern)
    helper-patterns =
      arg (arg-info hidden relevant) (var "_") ∷
      arg (arg-info hidden relevant) (var "_") ∷ []

    helper-term : Name → Term
    helper-term solution-name = def₀ solution-name

    helper-tactic : Name → Type → Name → Tactic
    helper-tactic record-name record-parameter-type solution-name hole = do
      n ← freshName "helper" -|
      Γ ← getContext -|
      catchTC (define (vArg n)
                      (helper-type record-name record-parameter-type)
                      [ clause helper-patterns (helper-term solution-name) ])
              (typeError ( strErr "error defining helper function" ∷
                           termErr (` Γ) ∷
                           []))
      ~|
      unify hole (helper-term solution-name)

    module _ (A : Set) where
      postulate
        trustMe : ∀ {α} {A : Set α} → A

      record R-independent-succeeds (a : Set) : Set where
        test : Set
        test = unquote (helper-tactic (quote R-independent-succeeds)
                                      (agda-sort (lit 0))
                                      (quote trustMe))
{-
      record R-dependent-fails (a : A) : Set where
        test : Set
        test = unquote (helper-tactic (quote R-dependent-fails)
                                      (var 0 [])
                                      (quote trustMe))
               {- Γ =
               arg (arg-info visible irrelevant)
               (def (quote R-dependent-fails)
                (arg (arg-info visible relevant) (var 0 []) ∷ []))
               ∷
               arg (arg-info hidden relevant) (var 0 []) ∷
               arg (arg-info hidden relevant) (agda-sort (lit 0)) ∷ []
               -}
-}


  module M₁₀ where
    open import Prelude
    open import Tactic.Reflection
    open import Tactic.Reflection.Quote
    open import Builtin.Reflection

    helper-type : Name → Type → Type
    helper-type record-name record-parameter-type =
      {-
      pi (arg (arg-info hidden relevant) (agda-sort (lit 0)))
      (abs "_"
      -}
       (pi (arg (arg-info hidden relevant) record-parameter-type)
        (abs "_"
         (pi
          (arg (arg-info visible irrelevant)
           (def record-name (arg (arg-info visible relevant) (var 0 []) ∷ [])))
          (abs "_" (agda-sort (lit 0)))))) -- )

    helper-patterns : List (Arg Pattern)
    helper-patterns =
      -- arg (arg-info hidden relevant) (var "_") ∷
      arg (arg-info hidden relevant) (var "_") ∷ []

    helper-term : Name → Term
    helper-term solution-name = def₀ solution-name

    helper-tactic : Name → Type → Name → Tactic
    helper-tactic record-name record-parameter-type solution-name hole = do
      n ← freshName "helper" -|
      Γ ← getContext -|
--      catchTC
        (define (vArg n)
                (helper-type record-name record-parameter-type)
                [ clause helper-patterns (helper-term solution-name) ])
{-
        (typeError ( strErr "error defining helper function" ∷
                     termErr (` Γ) ∷
                     []))
-}
      ~|
      unify hole (helper-term solution-name)

    module _ (A : Set) where
      postulate
        trustMe : ∀ {α} {A : Set α} → A

      record R-independent-succeeds (a : Set) : Set where
        test : Set
        test = unquote (helper-tactic (quote R-independent-succeeds)
                                      (agda-sort (lit 0))
                                      (quote trustMe))
{-
      record R-dependent-fails (a : A) : Set where
        test : Set
        test = unquote (helper-tactic (quote R-dependent-fails)
                                      (var 1 [])
                                      (quote trustMe))
               {- Γ =
               arg (arg-info visible irrelevant)
               (def (quote R-dependent-fails)
                (arg (arg-info visible relevant) (var 0 []) ∷ []))
               ∷
               arg (arg-info hidden relevant) (var 0 []) ∷
               arg (arg-info hidden relevant) (agda-sort (lit 0)) ∷ []
               -}
-}


  module M₁₁ where
    open import Prelude
    open import Tactic.Reflection
    open import Tactic.Reflection.Quote
    open import Builtin.Reflection

    postulate trustMe : ∀ {α} {A : Set α} → A

    module _ (A : Set) where
      postulate R : A → Set

      macro
        helper : Tactic
        helper hole = do
          n ← freshName "helper" -|
          define (vArg n)
                 (pi (arg (arg-info visible relevant)
                          (var 0 []))
                     (abs "_"
                          (pi (arg (arg-info visible irrelevant)
                                   (def (quote R) (arg (arg-info visible relevant) (var 0 []) ∷ [])))
                              (abs "_" (agda-sort (lit 0))))))
                 [ clause
                     (arg (arg-info visible relevant) (var "_") ∷ [])
                     (def (quote trustMe) [])
                 ]
          ~|
          unify hole (def n [])

      doppelganger : (x : A) → R x → Set
      doppelganger = trustMe

      test : (x : A) → R x → Set
      test = helper

  module M₁₂ where
    open import Prelude
    open import Tactic.Reflection
    open import Tactic.Reflection.Quote
    open import Builtin.Reflection

    macro
      showContext : Tactic
      showContext hole =
        Γ ← getContext -|
        typeError [ termErr (` Γ) ]

    module M (A : Set) where
      test-inside : Set
      test-inside = {!!} -- showContext -- arg (arg-info visible relevant) (agda-sort (lit 0)) ∷ []

      record R (a : A) : Set where
        inductive

        test-inside-R₁ : Set
        test-inside-R₁ = {!showContext!}
        {-
        arg (arg-info visible irrelevant)
        (def (quote R) (arg (arg-info visible relevant) (var 0 []) ∷ []))
        ∷
        arg (arg-info hidden relevant) (var 0 []) ∷
        arg (arg-info hidden relevant) (agda-sort (lit 0)) ∷ []
        -}

        test-inside-R₂ : A → Set
        test-inside-R₂ = {!showContext!}
{-
        field
          f : R a → R a

        test-f : R a → R a
        test-f = ?
-}

    test-outside₁ : (A : Set) → Set
    test-outside₁ a = {!showContext!} -- arg (arg-info visible relevant) (agda-sort (lit 0)) ∷ []

    test-outside₂ : (A : Set) → Set
    test-outside₂ = {!showContext!} -- []

{-
  getContext returns all the variables bound where the macro is applied, not distinguishing between those bound by a module and those by the function currently being defined. E.g. the getContext of the following examples are equivalent:

  example₁ : Set → Set
  example₁ x = ?

  module _ (A : Set) where
    example₂ = ?

  My current problem requires me to know how many of the context variables are defined by enclosing modules, so  I'd like to be able to distinguish the two cases in a macro and can think of at least two possible solutions.

  Solution 1: enhance reflection to E.g.
    getDistinguishedContext : TC (
-}
{-
/home/martin/Desktop/scratch/uses-postlude/Map.agda:68,19-35
error defining helper function
helper-type:
{A₁ : Set} {z z₁ : A₁} .(r : R z₁) (z₂ : A₁) (z₃ : z ≡ z)
(z₄ : z ≡ z₂) (A₂ : Set) →
Set

`helper-type:
pi (arg (arg-info hidden relevant) (agda-sort (lit 0)))
(abs "_"
 (pi (arg (arg-info hidden relevant) (var 0 []))
  (abs "_"
   (pi (arg (arg-info hidden relevant) (var 1 []))
    (abs "_"
     (pi
      (arg (arg-info visible irrelevant)
       (def (quote R) (arg (arg-info visible relevant) (var 0 []) ∷ [])))
      (abs "_"
       (pi (arg (arg-info visible relevant) (var 3 []))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (def (quote _≡_)
            (arg (arg-info hidden relevant) (def (quote lzero) []) ∷
             arg (arg-info hidden relevant) (var 4 []) ∷
             arg (arg-info visible relevant) (var 3 []) ∷
             arg (arg-info visible relevant) (var 3 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (def (quote _≡_)
              (arg (arg-info visible relevant) (var 4 []) ∷
               arg (arg-info visible relevant) (var 1 []) ∷ [])))
            (abs "_"
             (pi (arg (arg-info visible relevant) (agda-sort (lit 0)))
              (abs "_" (agda-sort (lit 0)))))))))))))))))

helper-patterns:
arg (arg-info hidden relevant) (var "_") ∷
arg (arg-info hidden relevant) dot ∷
arg (arg-info hidden relevant) (var "_") ∷
arg (arg-info visible irrelevant) (var "_") ∷
arg (arg-info visible relevant) (var "_") ∷
arg (arg-info visible relevant) (var "_") ∷
arg (arg-info visible relevant) (con (quote refl) []) ∷
arg (arg-info visible relevant) (var "_") ∷ []

helper-term: x≡x
`helper-term: var 0 []
gʳ:
just (agda-sort (lit 0))
Γʷ:
just
(arg (arg-info visible relevant)
 (def (quote _≡_)
  (arg (arg-info hidden relevant) (def (quote lzero) []) ∷
   arg (arg-info hidden relevant) (var 4 []) ∷
   arg (arg-info visible relevant) (var 3 []) ∷
   arg (arg-info visible relevant) (var 3 []) ∷ []))
 ∷
 arg (arg-info visible relevant) (var 3 []) ∷
 arg (arg-info visible irrelevant)
 (def (quote R) (arg (arg-info visible relevant) (var 0 []) ∷ []))
 ∷
 arg (arg-info hidden relevant) (var 1 []) ∷
 arg (arg-info hidden relevant) (var 0 []) ∷
 arg (arg-info hidden relevant) (agda-sort (lit 0)) ∷ [])

𝐺ʷ: agda-sort (lit 0)
l≡r: var 0 []
A: var 4 []
L: var 1 []
R:
var 1 []
Γᶜ:
arg (arg-info visible relevant)
(def (quote _≡_)
 (arg (arg-info hidden relevant) (def (quote lzero) []) ∷
  arg (arg-info hidden relevant) (var 3 []) ∷
  arg (arg-info visible relevant) (var 0 []) ∷
  arg (arg-info visible relevant) (var 0 []) ∷ []))
∷
arg (arg-info visible relevant) (var 2 []) ∷
arg (arg-info visible irrelevant)
(def (quote R) (arg (arg-info visible relevant) (var 0 []) ∷ []))
∷
arg (arg-info hidden relevant) (var 0 []) ∷
arg (arg-info hidden relevant) (agda-sort (lit 0)) ∷ []

𝐺: agda-sort (lit 0)
Γʷ/ᴬ
just (arg (arg-info hidden relevant) (agda-sort (lit 0)) ∷ [])

Γʷ/⁻ᴬ
just
(arg (arg-info visible relevant)
 (def (quote _≡_)
  (arg (arg-info hidden relevant) (def (quote lzero) []) ∷
   arg (arg-info hidden relevant) (var 4 []) ∷
   arg (arg-info visible relevant) (var 0 []) ∷
   arg (arg-info visible relevant) (var 0 []) ∷ []))
 ∷
 arg (arg-info visible relevant) (var 3 []) ∷
 arg (arg-info visible irrelevant)
 (def (quote R) (arg (arg-info visible relevant) (var 0 []) ∷ []))
 ∷ arg (arg-info hidden relevant) (var 1 []) ∷ [])

[iᶜ∣iᶜ∈FVᴬ] 4 ∷ []
[iᶜ∣iᶜ∉FVᴬ] 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
[iʷ]
0 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ []
when checking that the expression
unquote (reright (quoteTerm x≡x)) ? has type Set
-}
