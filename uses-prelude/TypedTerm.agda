module TypedTerm where
  open import Prelude
  open import Builtin.Reflection
  
  open import Container.Traversable
  
  open import Tactic.Reflection
  open import Tactic.Reflection.Quote
  open import Tactic.Deriving.Quotable

  
  mutual
    data TypedTerm : Set where
      var           : Type → (x : Nat) (args : List (Arg TypedTerm)) → TypedTerm
      con           : Type → (c : Name) (args : List (Arg TypedTerm)) → TypedTerm
      def           : Type → (f : Name) (args : List (Arg TypedTerm)) → TypedTerm
      lam           : Type → (v : Visibility) (t : Abs TypedTerm) → TypedTerm
      pat-lam       : Type → (cs : List TypedClause) (args : List (Arg TypedTerm)) → TypedTerm
      pi            : Type → (a : Arg TypedType) (b : Abs TypedType) → TypedTerm
      agda-sort     : Type → (s : TypedSort) → TypedTerm
      lit           : Type → (l : Literal) → TypedTerm
      meta          : Type → (x : Meta) → List (Arg TypedTerm) → TypedTerm
      unknown       : Type → TypedTerm

    TypedType : Set
    TypedType = TypedTerm

    data TypedClause : Set where
      clause : List (Arg Pattern) → TypedTerm → TypedClause
      absurd-clause : List (Arg Pattern) → TypedClause

    data TypedSort : Set where
      set     : (t : TypedTerm) → TypedSort
      lit     : (n : Nat) → TypedSort
      unknown : TypedSort

  mutual
    {-# TERMINATING #-}
    termTypedClause : TypedClause → Clause
    termTypedClause (clause ps x) = clause ps (termTypedTerm x)
    termTypedClause (absurd-clause x₁) = absurd-clause x₁
    
    {-# TERMINATING #-}
    termTypedSort : TypedSort → Sort
    termTypedSort (set t) = set (termTypedTerm t)
    termTypedSort (lit n) = lit n
    termTypedSort unknown = unknown
    
    {-# TERMINATING #-}
    termTypedTerm : TypedTerm → Term
    termTypedTerm (var _ x args) = var x (fmap termTypedTerm <$> args)
    termTypedTerm (con _ c args) = con c (fmap termTypedTerm <$> args)
    termTypedTerm (def _ f args) = def f (fmap termTypedTerm <$> args)
    termTypedTerm (lam _ v (abs s t)) = lam v (abs s (termTypedTerm t))
    termTypedTerm (pat-lam _ cs args) = pat-lam (fmap termTypedClause cs) (fmap termTypedTerm <$> args) where
    termTypedTerm (pi _ a b) = pi (fmap termTypedTerm a) (fmap termTypedTerm b)
    termTypedTerm (agda-sort _ s) = agda-sort (termTypedSort s) where
    termTypedTerm (lit _ l) = lit l
    termTypedTerm (meta _ m args) = meta m (fmap termTypedTerm <$> args)
    termTypedTerm (unknown _) = unknown

  typeTypedTerm : TypedTerm → Type
  typeTypedTerm (var y x₁ args) = y
  typeTypedTerm (con y c args) = y
  typeTypedTerm (def y f args) = y
  typeTypedTerm (lam y v t) = y
  typeTypedTerm (pat-lam y cs args) = y
  typeTypedTerm (pi y a b) = y
  typeTypedTerm (agda-sort y s) = y
  typeTypedTerm (lit y l) = y
  typeTypedTerm (meta y x₁ x₂) = y
  typeTypedTerm (unknown y) = y
      
  private
    deriveQuotableTermTypes : Vec Name _ → TC ⊤
    deriveQuotableTermTypes is =
      do ts  := quote TypedTerm ∷ quote TypedClause ∷ quote TypedSort ∷ [] ofType Vec Name _
      -| its := _,_ <$> is <*> ts
      -| traverse (uncurry declareQuotableInstance) its
      ~| traverse (uncurry defineQuotableInstance)  its
      ~| pure _

  {-# TERMINATING #-}
  unquoteDecl QuotableTypedTerm QuotableTypedClause QuotableTypedSort =
    deriveQuotableTermTypes (QuotableTypedTerm ∷ QuotableTypedClause ∷ QuotableTypedSort ∷ [])
  
  {-# TERMINATING #-}
  inferTyped : Term → TC TypedTerm
  inferTyped e = inferType e >>= λ y → inferTyped' y e where
    inferTyped' : Type → Term → TC TypedTerm
    inferTyped' y (var x args) = var y x <$> traverse id (traverse inferTyped <$> args)
    inferTyped' y (con c args) = con y c <$> traverse id (traverse inferTyped <$> args)
    inferTyped' y (def f args) = def y f <$> traverse id (traverse inferTyped <$> args)
    inferTyped' y (lam v (abs s t)) = extendContext (arg (arg-info v relevant) unknown) $ inferTyped t >>= λ T → return (lam y v (abs s T)) -- YELLOW: (return ∘ lam y v ∘ abs s) -- TODO
    inferTyped' y (pat-lam cs args) = pat-lam y <$> (traverse id $ inferClause <$> cs) <*> (traverse id (traverse inferTyped <$> args)) -- TODO
      where
      inferClause : Clause → TC TypedClause
      inferClause (clause ps t) = clause ps <$> inferTyped t
      inferClause (absurd-clause ps) = return $ absurd-clause ps
    inferTyped' y (pi a b) = pi y <$> (traverse id $ inferTyped <$> a) <*> (extendContext a $ traverse id $ inferTyped <$> b)
    inferTyped' y (agda-sort s) = agda-sort y <$> inferSort s where
      inferSort : Sort → TC TypedSort
      inferSort (set t) = set <$> inferTyped t
      inferSort (lit n) = return $ lit n
      inferSort unknown = return $ unknown
    inferTyped' y (lit l) = return $ lit y l
    inferTyped' y (meta m args) = meta y m <$> traverse id (traverse inferTyped <$> args)
    inferTyped' y unknown = return $ unknown y
