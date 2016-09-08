open import Prelude
open import Tactic.Reflection

data D : Set where
  d : D

term₀ : Term
term₀ = pat-lam [ clause (vArg (con (quote d) []) ∷ []) $ var₀ 0 ]
                []

term₁ : Term
term₁ = pat-lam [ clause (vArg (con (quote d) []) ∷ []) $ var₀ 0 ]
                (vArg (var₀ 0) ∷ [])

macro
  do-unify₀ : Tactic
  do-unify₀ = flip unify term₀

  do-unify₁ : Tactic
  do-unify₁ = flip unify term₁

test₀ : D → D
test₀ d' = case_of_ {lzero} {lzero} {D} {D} d' do-unify₀

test₁ : D → D
test₁ d' = case_of_ {lzero} {lzero} {D} {D} d' do-unify₁ -- unsolved metas

open import Tactic.Reflection.Quote

macro
  showDefinition : Name → Tactic
  showDefinition n hole = do
    cs ← getClauses n -|
    typeError [ termErr (` cs) ]

foo : Set
foo = {!showDefinition test₀!}
{- Results of showDefinition below. Notice that the pat-lam matches that from term₁, not term₀!

   clause (arg (arg-info visible relevant) (var "d'") ∷ [])
   (def (quote case_of_)
    (arg (arg-info hidden relevant) (def (quote lzero) []) ∷
     arg (arg-info hidden relevant) (def (quote lzero) []) ∷
     arg (arg-info hidden relevant) (def (quote D) []) ∷
     arg (arg-info hidden relevant) (def (quote D) []) ∷
     arg (arg-info visible relevant) (var 0 []) ∷
     arg (arg-info visible relevant)
     -- =============>
     (pat-lam
      (clause
       (arg (arg-info visible relevant) (var "d'") ∷
        arg (arg-info visible relevant) (con (quote d) []) ∷ [])
       (var 0 [])
       ∷ [])
      (arg (arg-info visible relevant) (var 0 []) ∷ []))
      -- <============
     ∷ []))
   ∷ []
-}
