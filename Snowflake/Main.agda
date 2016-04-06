module Snowflake.Main where

open import Snowflake.Prelude

{- NO INSTANCE ERROR
open import Prelude using (id {-syntax ofType-})
-}

test₀ : 𝕃→𝑳 (reorder [abcd] (0 ∷ₗ 0 ∷ₗ 0 ∷ₗ 0 ∷ₗ ∅)) ≡ 𝕃→𝑳 [abcd]
test₀ = refl

--test₁ : 𝕃→𝑳 (reorder [abcd] (3 ∷ₗ 2 ∷ₗ 0 ∷ₗ 0 ∷ₗ ∅)) ≡ 𝕃→𝑳 [dcab]
--test₁ = refl

--test₂ : 𝕃→𝑳 (reorder [abcd] (3 ∷ₗ 2 ∷ₗ 1 ∷ₗ 0 ∷ₗ ∅)) ≡ 𝕃→𝑳 [dcba]
--test₂ = refl
