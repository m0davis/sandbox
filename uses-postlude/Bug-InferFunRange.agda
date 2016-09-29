module Bug-InferFunRange where

-- Why does `inferFunRange` fail in the code below? I expected Agda to report "inferFunRange succeeded (x : A) → F x → Set".

module M₁ where
  open import Prelude
  open import Tactic.Reflection

  macro
    test-inferFunRange : Tactic
    test-inferFunRange hole = do
      goal ← inferFunRange hole -|
      typeError ( strErr "inferFunRange succeeded" ∷ termErr goal ∷ [] )

  bar : Nat
  bar = 0

  record R (A : Set) : Set₁ where
    field
      F : A → Set
      a : A

    foo : (x : A) → F x → Set
    foo = case bar of (λ _ → test-inferFunRange {!!})
    {- Error:
         A → Set !=< Set of type Set₁
         when checking that the expression F has type Set
    -}

module M₂ where
  open import Prelude
  open import Tactic.Reflection


  inferFunRange' : Term → TC Type
  inferFunRange' hole = unPi =<< forceFun =<< inferType hole where
    unPi : Type → TC Type
    unPi (pi p (abs a (meta x xs))) = commitTC >> normalise (pi p (abs a (meta x xs))) >>= return
    unPi (pi _ (abs _ b)) = maybe (typeError (strErr "Must be applied in a non-dependent function position" ∷ termErr b ∷ [])) pure $ strengthen 1 b
    unPi x = typeError (strErr "Invalid goal" ∷ termErr x ∷ [])


  macro
    test-inferFunRange : Tactic
    test-inferFunRange hole = do
      goal ← inferFunRange hole -|
      commitTC ~|
      typeError ( strErr "inferFunRange succeeded" ∷ termErr goal ∷ [] )

  bar : Nat
  bar = 0

  record R (A : Set) : Set₁ where
    field
      F : A → Set
      a : A

    foo : (x : A) → F x → Set
    foo = case bar of (λ _ → test-inferFunRange {!!})
    {- Error:
         A → Set !=< Set of type Set₁
         when checking that the expression F has type Set
    -}

module M₃ where
  open import Agda.Builtin.Reflection
  open import Agda.Builtin.Unit
  open import Agda.Builtin.List
  open import Agda.Builtin.Equality

  infixl 4 _>>=_
  _>>=_ = bindTC

  macro
    qType : Term → Term → TC ⊤
    qType t hole = inferType t >>= quoteTC >>= unify hole

  postulate
    X : Set
    x y z : X

  record R (A B : Set) : Set₁ where
    field
      F : X → X → X → Set

    bar : F x y z → Term
    bar fx = {!qType fx!}  -- result: R.F z   (x y are dropped)
