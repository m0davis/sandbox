module RerightDoneRight where
  module ParameterisedByListLabel where
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
        
      Context : Set
      Context = List Label

      data Sort (Γ : Context) : Set
      data Clause (Γ : Context) : Set
      data Term (Γ : Context) : Set
      Type = Term
   
      data Term (Γ : Context) where
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
   
      data Sort (Γ : Context) where
        set     : (t : Term Γ) → Sort Γ
        lit     : (n : Nat) → Sort Γ
        unknown : Sort Γ

      data Clause (Γ : Context) where
        clause        : (ps : List (Arg Pattern)) (Γₚₛ : Context) (t : Term (Γₚₛ ++ Γ)) → Clause Γ
        absurd-clause : (ps : List (Arg Pattern)) → Clause Γ

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
               ; Context to LabeledContext
               )

    open import Control.Monad.State
    open import Control.Monad.Identity

    infix 1 _⟶ₜ_
    record _⟶ₜ_ (A : Set) (B : LabeledContext → Set) : Set where
      field
        applyₜ : (Γ : LabeledContext) → A → StateT Label Maybe (B Γ)
   
    open _⟶ₜ_ {{...}}

    infix 1 _⟶ₚ_
    record _⟶ₚ_ (A : Set) (B : Set) : Set where
      field
        applyₚ : A → StateT LabeledContext (StateT Label Identity) B

    open _⟶ₚ_ {{...}}

    ∃ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
    ∃ = Σ _

    instance
      TListArgTerm : List (Arg Term) ⟶ₜ List ∘ Arg ∘ LabeledTerm

      {-# TERMINATING #-}
      TTerm : Term ⟶ₜ LabeledTerm
      TSort : Sort ⟶ₜ LabeledSort
      TClause : Clause ⟶ₜ LabeledClause
      
      TArgTerm : Arg Term ⟶ₜ Arg ∘ LabeledTerm
      TAbsTerm : Abs Term ⟶ₜ Abs ∘ LabeledTerm

      TPattern : Pattern ⟶ₚ LabeledPattern
      TArgPattern : Arg Pattern ⟶ₚ Arg LabeledPattern
      TListArgPattern : List (Arg Pattern) ⟶ₚ List (Arg LabeledPattern)
   
    _⟶ₜ_.applyₜ TListArgTerm Γ [] = pure []
    _⟶ₜ_.applyₜ TListArgTerm Γ (x ∷ xs) = do
      x' ← applyₜ Γ x -|
      xs' ← applyₜ Γ xs -|
      pure (x' ∷ xs')
    
    _⟶ₜ_.applyₜ TTerm Γ (var x args) = do
      args' ← applyₜ Γ args -|
      lift $ var <$> index Γ x <*> pure args'
    _⟶ₜ_.applyₜ TTerm Γ (con c args) = applyₜ Γ args >>= lift ∘ pure ∘ con c
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
      PS ← mapStateT (just ∘ runIdentity) $ runStateT (applyₚ ps) [] -|
      ps' := fst PS -|
      Γ' := snd PS -|
      t' ← applyₜ (Γ' ++ Γ) t -|
      lift $ pure $ clause ps' Γ' t'
    _⟶ₜ_.applyₜ TClause Γ (absurd-clause ps) = (mapStateT (just ∘ runIdentity) $ runStateT (applyₚ ps) []) >>= lift ∘′ pure ∘ absurd-clause ∘ fst
    
    _⟶ₜ_.applyₜ TArgTerm Γ t = traverse (applyₜ Γ) t
    
    _⟶ₜ_.applyₜ TAbsTerm Γ t = traverse (applyₜ Γ) t
    
    _⟶ₚ_.applyₚ TPattern (con c ps) = applyₚ ps >>= λ ps' → lift $ lift $ mkIdentity $ con c ps'
    _⟶ₚ_.applyₚ TPattern dot = lift $ pure dot
    _⟶ₚ_.applyₚ TPattern (var s) = lift get >>= λ ℓ → modify (ℓ ∷_) >> lift (modify nextLabel) >> (lift ∘′ lift ∘ mkIdentity $ var ℓ s)
    _⟶ₚ_.applyₚ TPattern (lit l) = lift $ pure $ lit l
    _⟶ₚ_.applyₚ TPattern (proj f) = lift $ pure $ proj f
    _⟶ₚ_.applyₚ TPattern absurd = lift $ pure absurd
   
    _⟶ₚ_.applyₚ TArgPattern p = traverse applyₚ p
    
    _⟶ₚ_.applyₚ TListArgPattern ps = traverse applyₚ ps

    open import Tactic.Reflection
    open import Tactic.Reflection.Quote
    macro
      mac : Tactic
      mac hole = 
        goal ← inferType hole -|
        app := applyₜ [] goal -|
        h := maybe unknown id $ fst <$> runStateT app 0 -|
        g ← quoteTC (h ofType LabeledTerm []) -|
        (typeError [ termErr g ] ofType TC ⊤)

    foo : (A : Set) → (a b : A) → a ≡ b
    foo = {!mac!} where
      open Reflection/Label
