open import Prelude
open import Builtin.Reflection

macro
  debugRewriteDefinition : Name → Tactic
  debugRewriteDefinition n hole = do
    n-clauses ← getClauses n -|
    case index n-clauses 0 of λ {
       (just (clause _ (def rewrite-name _))) → getDefinition rewrite-name >> return _
     ; _ → return _
     }

test : (A B : Set) (A≡B : A ≡ B) → Set
test A B A≡B rewrite A≡B = ?

error : Set
error = debugRewriteDefinition test
