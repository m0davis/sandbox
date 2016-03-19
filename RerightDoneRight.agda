module RerightDoneRight where
  module Reflection/Label (Label : Set) where
    open import Agda.Builtin.Reflection hiding (Term; Type; Sort; Clause; Pattern)
    open import Prelude
 
    data Pattern : Set where
      con    : (c : Name) (ps : List (Arg Pattern)) → Pattern
      dot    : Pattern
      var    : (ℓ : Label) → (s : String)  → Pattern
      lit    : (l : Literal) → Pattern
      proj   : (f : Name)    → Pattern
      absurd : Pattern
      
    Context : Nat → Set
    Context = Vec Label
 
    data Sort {∣Γ∣} (Γ : Context ∣Γ∣) : Set
    data Clause {∣Γ∣} (Γ : Context ∣Γ∣) : Set
    data Term {∣Γ∣} (Γ : Context ∣Γ∣) : Set
    Type = Term
 
    data Term {∣Γ∣} (Γ : Context ∣Γ∣) where
      var           : (x : Label) (args : List (Arg (Term Γ))) → Term Γ
      con           : (c : Name) (args : List (Arg (Term Γ))) → Term Γ
      def           : (f : Name) (args : List (Arg (Term Γ))) → Term Γ
      lam           : (ℓ : Label) (v : Visibility) (t : Abs (Term (ℓ ∷ Γ))) → Term Γ
      pat-lam       : (cs : List (Clause Γ)) → Term Γ
      pi            : (ℓ : Label) (a : Arg (Type Γ)) (b : Abs (Type (ℓ ∷ Γ))) → Term Γ
      agda-sort     : (s : Sort Γ) → Term Γ
      lit           : (l : Literal) → Term Γ
      meta          : (x : Meta) (args : List (Arg (Term Γ))) → Term Γ
      unknown       : Term Γ
 
    data Sort {∣Γ∣} (Γ : Context ∣Γ∣) where
      set     : (t : Term Γ) → Sort Γ
      lit     : (n : Nat) → Sort Γ
      unknown : Sort Γ
 
    data Clause {∣Γ∣} (Γ : Context ∣Γ∣) where
      clause        : (ps : List (Arg Pattern)) → ∀ {∣Γₚₛ∣} → (Γₚₛ : Context ∣Γₚₛ∣) (t : Term (Γₚₛ v++ Γ)) → Clause Γ
      absurd-clause : (ps : List (Arg Pattern)) → Clause Γ

  module Label=Nat where
    open import Prelude
    open import Agda.Builtin.Reflection
    open import Container.Traversable
   
    Label : Set
    Label = Nat
   
    nextLabel : Label → Label
    nextLabel = suc
   
    firstLabel : Label
    firstLabel = 0
   
    open Reflection/Label Label
      renaming ( Term to LabeledTerm
               ; Type to LabeledType
               ; Sort to LabeledSort
               ; Clause to LabeledClause
               ; Pattern to LabeledPattern
               ; Context to ContextLabels
               )
      public
   
    open import Control.Monad.State
    open import Control.Monad.Identity
   
    infix 1 _⟶ₜ_
    record _⟶ₜ_ (A : Set) (B : ∀ {∣Γ∣} → ContextLabels ∣Γ∣ → Set) : Set where
      field
        applyₜ : ∀ {∣Γ∣} → (Γ : ContextLabels ∣Γ∣) → A → StateT Label Maybe (B Γ)
   
    open _⟶ₜ_ ⦃ … ⦄
   
    infix 1 _⟶ₚ_
    record _⟶ₚ_ (A : Set) (B : Set) : Set where
      field
        applyₚ : A → StateT (∃ λ ∣Γ∣ → ContextLabels ∣Γ∣) (StateT Label Identity) B
   
    open _⟶ₚ_ ⦃ … ⦄
   
    instance
      TListArgTerm : List (Arg Term) ⟶ₜ List ∘ Arg ∘ LabeledTerm
      --TListArgTerm′ : List (Arg Term) ⟶ₜ List ∘ Arg ∘ LabeledTerm
   
      {-# TERMINATING #-}
      TTerm : Term ⟶ₜ LabeledTerm
      TSort : Sort ⟶ₜ LabeledSort
      TClause : Clause ⟶ₜ LabeledClause
      
      TArgTerm : Arg Term ⟶ₜ Arg ∘ LabeledTerm
      TAbsTerm : Abs Term ⟶ₜ Abs ∘ LabeledTerm
   
      TPattern : Pattern ⟶ₚ LabeledPattern
      TArgPattern : Arg Pattern ⟶ₚ Arg LabeledPattern
      TListArgPattern : List (Arg Pattern) ⟶ₚ List (Arg LabeledPattern)
   
    _⟶ₜ_.applyₜ TListArgTerm Γ xs = traverse (applyₜ Γ) xs
    {-
    _⟶ₜ_.applyₜ TListArgTerm Γ [] = pure []
    _⟶ₜ_.applyₜ TListArgTerm Γ (x ∷ xs) = do
      x' ← applyₜ Γ x -|
      xs' ← applyₜ Γ xs -|
      pure (x' ∷ xs')
    -}
   
    open import Control.Monad.Zero
    _⟶ₜ_.applyₜ TTerm {∣Γ∣} Γ (var x args) = do
      args' ← applyₜ Γ args -|
      guard (decBool $ lessNat x ∣Γ∣) (do
        x' := natToFin x -|
        lift $ var (indexVec Γ x') <$> pure args')
    _⟶ₜ_.applyₜ TTerm Γ (con c args) = con c <$> traverse (applyₜ Γ) args -- applyₜ Γ args >>= lift ∘ pure ∘ con c
    _⟶ₜ_.applyₜ TTerm Γ (def f args) = applyₜ Γ args >>= lift ∘ pure ∘ def f
    _⟶ₜ_.applyₜ TTerm Γ (lam v t) = do
      ℓ ← get -|
      modify nextLabel ~|
      t' ← applyₜ {B = Abs ∘ LabeledTerm} (ℓ ∷ Γ) t -|
      lift $ lam ℓ v <$> pure t'
    _⟶ₜ_.applyₜ TTerm Γ (pat-lam cs _) = pat-lam <$> traverse (applyₜ Γ) cs
    _⟶ₜ_.applyₜ TTerm Γ (pi a b) = get >>= λ ℓ → modify nextLabel >> pi ℓ <$> applyₜ Γ a <*> applyₜ (ℓ ∷ Γ) b
    _⟶ₜ_.applyₜ TTerm Γ (agda-sort s) = agda-sort <$> applyₜ Γ s
    _⟶ₜ_.applyₜ TTerm Γ (lit l) = pure $ lit l
    _⟶ₜ_.applyₜ TTerm Γ (meta x args) = meta x <$> applyₜ Γ args
    _⟶ₜ_.applyₜ TTerm Γ unknown = pure unknown
   
    _⟶ₜ_.applyₜ TSort Γ (set t) = set <$> applyₜ Γ t
    _⟶ₜ_.applyₜ TSort Γ (lit n) = pure $ lit n
    _⟶ₜ_.applyₜ TSort Γ unknown = pure unknown
    
    _⟶ₜ_.applyₜ TClause Γ (clause ps t) = do
      PS ← mapStateT (just ∘ runIdentity) $ runStateT (applyₚ ps) (0 , []) -|
      ps' := fst PS -|
      Γ' := snd (snd PS) -|
      t' ← applyₜ (Γ' v++ Γ) t -|
      lift $ pure $ clause ps' Γ' t'
    _⟶ₜ_.applyₜ TClause Γ (absurd-clause ps) = (mapStateT (just ∘ runIdentity) $ runStateT (applyₚ ps) (0 , [])) >>= lift ∘′ pure ∘ absurd-clause ∘ fst
    
    _⟶ₜ_.applyₜ TArgTerm Γ t = traverse (applyₜ Γ) t
    
    _⟶ₜ_.applyₜ TAbsTerm Γ t = traverse (applyₜ Γ) t
    
    _⟶ₚ_.applyₚ TPattern (con c ps) = applyₚ ps >>= λ ps' → lift $ lift $ mkIdentity $ con c ps'
    _⟶ₚ_.applyₚ TPattern dot = lift $ pure dot
    _⟶ₚ_.applyₚ TPattern (var s) = lift get >>= λ ℓ → modify (suc *** (ℓ ∷_)) >> lift (modify nextLabel) >> (lift ∘′ lift ∘ mkIdentity $ var ℓ s)
    _⟶ₚ_.applyₚ TPattern (lit l) = lift $ pure $ lit l
    _⟶ₚ_.applyₚ TPattern (proj f) = lift $ pure $ proj f
    _⟶ₚ_.applyₚ TPattern absurd = lift $ pure absurd
   
    _⟶ₚ_.applyₚ TArgPattern p = traverse applyₚ p
    
    _⟶ₚ_.applyₚ TListArgPattern ps = traverse applyₚ ps

  module Context where
    open import Prelude
    open import Control.Monad.State
    open import Tactic.Reflection
    open import Tactic.Reflection.Quote

    open Label=Nat

    open _⟶ₜ_ ⦃ … ⦄

    data TCContext : ∀ {∣Γ∣} → ContextLabels ∣Γ∣ → Set where
      [] : TCContext []
      _∷_ : ∀ {∣Γ∣} {Γ : ContextLabels ∣Γ∣} → (τ : Label × Arg (LabeledTerm Γ)) → TCContext Γ → TCContext (fst τ ∷ Γ)
   
    mkTCContext₀' : Arg Type → ∀ {∣Γ∣} → {Γ : ContextLabels ∣Γ∣} → TCContext Γ → StateT Label Maybe (∃ λ ℓ → TCContext (ℓ ∷ Γ))
    mkTCContext₀' τ {Γ = Γ} TCΓ = do
      τ' ← applyₜ Γ τ -|
      ℓ ← modify nextLabel -|
      pure $ ℓ , ((ℓ , τ') ∷ TCΓ)
   
    mkTCContext' : List (Arg Type) → StateT Label Maybe (∃ λ ∣Γ∣ → ∃ λ Γ → TCContext {∣Γ∣} Γ)
    mkTCContext' [] = stateT (λ ℓ → just ((0 , [] , []) , ℓ))
    mkTCContext' (t ∷ ts) = do
      tcs ← mkTCContext' ts -|
      ts' := snd $ snd tcs -|
      tcc ← mkTCContext₀' t ts' -|
      ∣Γ∣ := fst tcc -|
      Γ := snd tcc -|
      pure (_ , (_ , Γ))

    record Context : Set where
      constructor Ctx
      field
        {∣LC∣} : Nat
        {LC} : ContextLabels ∣LC∣
        G : TCContext LC

    getContext'' : TC (Maybe Context)
    getContext'' = do
     Γ ← getContext -|
     g := evalStateT (mkTCContext' Γ) firstLabel -|
     pure $ maybe nothing (λ x → let x1 = fst x
                                  in let x2 = snd x in let x21 = fst x2 in let x22 = snd x2 in pure (Ctx x22)) g


    macro
      testContext' : Tactic
      testContext' hole = do
        C ← quoteTC =<< getContext'' -|
        typeError ( termErr C ∷ [] )
   
    foo : ∀ {α} (A : Set α) → (a b : A) → a ≡ b
    foo A a b = {!testContext'!}
