module Snowflake.Main where

open import Snowflake.Prelude

test₀ : 𝕃→𝑳 (reorder [abcd] (0 ∷ₗ 0 ∷ₗ 0 ∷ₗ 0 ∷ₗ ∅)) ≡ 𝕃→𝑳 [abcd]
test₀ = refl

-- test₁ : 𝕃→𝑳 (reorder [abcd] (3 ∷ₗ 2 ∷ₗ 0 ∷ₗ 0 ∷ₗ ∅)) ≡ 𝕃→𝑳 [dcab]
-- test₁ = refl

test₂ : 𝕃→𝑳 (reorder [abcd] (3 ∷ₗ 2 ∷ₗ 1 ∷ₗ 0 ∷ₗ ∅)) ≡ 𝕃→𝑳 [dcba]
test₂ = refl

-- test₂-1 : 𝕃→𝑳 (raiseFromTopBy 3 3 [abcd]) ≡ 𝕃→𝑳 [dcba]
-- test₂-1 = {!refl!}

-- test₂-2 : 𝕃→𝑳 (raiseFromTopBy 3 1 (raiseFromTopBy 3 3 [abcd])) ≡ 𝕃→𝑳 [dcba]
-- test₂-2 = {!refl!}

-- test₂-1a : 𝕃→𝑳 (raiseBottomBy 3 [abcd]) ≡ 𝕃→𝑳 [dcba]
-- test₂-1a = {!refl!}

-- test₂-2a : 𝕃→𝑳 (raiseBottomBy 2 (raiseBottomBy 3 [abcd])) ≡ 𝕃→𝑳 [dcba]
-- test₂-2a = {!refl!}

-- test₂-3b : 𝕃→𝑳 (raiseFromBottom 2 ∘ raiseFromBottom 1 ∘ raiseFromBottom 0 $ [abcd]) ≡ 𝕃→𝑳 [dcba]
-- test₂-3b = {!refl!}

-- test₂-3b-0' : (raiseFromBottom 0 $ [abcd]) ≡ [dcba]
-- test₂-3b-0' = {!refl!}

-- test₂-4b : 𝕃→𝑳 (raiseFromBottom 0 ∘ raiseFromBottom 2 ∘ raiseFromBottom 1 ∘ raiseFromBottom 0 $ [abcd]) ≡ 𝕃→𝑳 [dcba]
-- test₂-4b = {!refl!}

-- test₂-5b : 𝕃→𝑳 (raiseFromBottom 1 ∘ raiseFromBottom 0 ∘ raiseFromBottom 2 ∘ raiseFromBottom 1 ∘ raiseFromBottom 0 $ [abcd]) ≡ 𝕃→𝑳 [dcba]
-- test₂-5b = {!refl!}

-- test₂-5b-0 : 𝕃→𝑳 (raiseFromBottom 0 ∘ raiseFromBottom 2 ∘ raiseFromBottom 1 ∘ raiseFromBottom 0 $ [abcd]) ≡ 𝕃→𝑳 [dcba]
-- test₂-5b-0 = {!refl!}

-- test₂-5b-0' : (raiseFromBottom 0 ∘ raiseFromBottom 2 ∘ raiseFromBottom 1 ∘ raiseFromBottom 0 $ [abcd]) ≡ [dcba]
-- test₂-5b-0' = {!refl!}

-- test₂-5b-1 : 𝕃→𝑳 (rotateDownBy 1 ∘ raiseFromBottom 0 ∘ raiseFromBottom 2 ∘ raiseFromBottom 1 ∘ raiseFromBottom 0 $ [abcd]) ≡ 𝕃→𝑳 [dcba]
-- test₂-5b-1 = {!refl!}

-- test₂-5b-2 : 𝕃→𝑳 (swapTop ∘ rotateDownBy 1 ∘ raiseFromBottom 0 ∘ raiseFromBottom 2 ∘ raiseFromBottom 1 ∘ raiseFromBottom 0 $ [abcd]) ≡ 𝕃→𝑳 [dcba]
-- test₂-5b-2 = {!refl!}

-- test₂-5b-3 : 𝕃→𝑳 (rotateDownBy 3 ∘ swapTop ∘ rotateDownBy 1 ∘ raiseFromBottom 0 ∘ raiseFromBottom 2 ∘ raiseFromBottom 1 ∘ raiseFromBottom 0 $ [abcd]) ≡ 𝕃→𝑳 [dcba]
-- test₂-5b-3 = {!refl!}

-- test₂-6-0 : ([abcd]) ≡ [dcba]
-- test₂-6-0 = {!refl!}

-- test₂-6-1 : (rotateDown $ [abcd]) ≡ [dcba]
-- test₂-6-1 = {!refl!}

-- test₂-6-2 : (swapTop ∘ rotateDown $ [abcd]) ≡ [dcba]
-- test₂-6-2 = {!refl!}

-- test₂-6-3 : (rotateDown ∘ swapTop ∘ rotateDown $ [abcd]) ≡ [dcba]
-- test₂-6-3 = {!refl!}

-- test₂-6-4 : (rotateDown ∘ rotateDown ∘ swapTop ∘ rotateDown $ [abcd]) ≡ [dcba]
-- test₂-6-4 = {!refl!}


-- test₂-6-5 : (rotateDown ∘ rotateDown ∘ rotateDown ∘ swapTop ∘ rotateDown $ [abcd]) ≡ [dcba]
-- test₂-6-5 = {!refl!} -- C-u C-u C-c C-.  : TODO this is getting very big

-- -- TODO takes a long time to typecheck
-- {-
-- test₂-7-5 : 𝕃→𝑳 (rotateDown ∘ rotateDown ∘ rotateDown ∘ rotateDown ∘
--                  rotateDown ∘ rotateDown ∘ rotateDown ∘ rotateDown ∘
--                  rotateDown ∘ rotateDown ∘ rotateDown ∘ rotateDown ∘
--                  rotateDown ∘ rotateDown ∘ rotateDown ∘ rotateDown ∘
--                  rotateDown ∘ rotateDown ∘ rotateDown ∘ rotateDown $
--                  [abcd]) ≡ 𝕃→𝑳 [abcd]
-- test₂-7-5 = {!refl!}
-- -}

-- -- but this is fast to typecheck
-- test₂-7-5' : 𝕃→𝑳 (rotateDown ( rotateDown ( rotateDown ( rotateDown (
--                   rotateDown ( rotateDown ( rotateDown ( rotateDown (
--                   rotateDown ( rotateDown ( rotateDown ( rotateDown (
--                   rotateDown ( rotateDown ( rotateDown ( rotateDown (
--                   rotateDown ( rotateDown ( rotateDown ( rotateDown (
--                   [abcd]))))))))))))))))))))) ≡ 𝕃→𝑳 [abcd]
-- test₂-7-5' = {!refl!} -- C-u C-u C-c C-.  : TODO this is getting very big
