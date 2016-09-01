module Snowflake.Main where

open import Snowflake.Prelude

-- -- trivial
-- test₀ : 𝕃→𝑳 (reorder [abcd] (0 ∷ₗ 0 ∷ₗ 0 ∷ₗ 0 ∷ₗ ∅)) ≡ 𝕃→𝑳 [abcd]
-- test₀ = refl
--  
-- -- memory hog
-- test₁ : 𝕃→𝑳 (reorder [abcd] (3 ∷ₗ 2 ∷ₗ 1 ∷ₗ 0 ∷ₗ ∅)) ≡ 𝕃→𝑳 [dcab]
-- test₁ = {!refl!}
--  
-- -- memory hog
-- test₁-raw₁ : 𝕃→𝑳 (raiseFromTopBy 3 0 (raiseFromTopBy 3 1 (raiseFromTopBy 3 2 (raiseFromTopBy 3 3 [abcd])))) ≡ 𝕃→𝑳 [dcba]
-- test₁-raw₁ = {!refl!}
--  
-- -- memory hog
-- test₁-raw₂ : 𝕃→𝑳 (raiseBottomBy 1 (raiseBottomBy 2 (raiseBottomBy 3 [abcd]))) ≡ 𝕃→𝑳 [dcba]
-- test₁-raw₂ = {!refl!}
--  
-- -- memory hog
-- test₁-raw₃ : 𝕃→𝑳 (raiseFromBottom 0 (raiseFromBottom 1 (raiseFromBottom 0 (raiseFromBottom 2 (raiseFromBottom 1 (raiseFromBottom 0 [abcd])))))) ≡ 𝕃→𝑳 [dcba]
-- test₁-raw₃ = {!refl!}
--  
-- -- memory hog
-- test₁-raw₄ : 𝕃→𝑳 (rotateDownBy 2 (swapTop (rotateDownBy 2 (rotateDownBy 1 (swapTop (rotateDownBy 3 (rotateDownBy 2 (swapTop (rotateDownBy 2 (rotateDownBy 0 (swapTop (rotateDownBy 4 (rotateDownBy 1 (swapTop (rotateDownBy 3 (rotateDownBy 2 (swapTop (rotateDownBy 2 [abcd])))))))))))))))))) ≡ 𝕃→𝑳 [dcba]
-- test₁-raw₄ = {!refl!}
--  
-- -- memory hog
-- test₁-raw₅ : 𝕃→𝑳 (rotateDown (rotateDown (swapTop (rotateDown (rotateDown (rotateDown (swapTop (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (swapTop (rotateDown (rotateDown (swapTop (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (swapTop (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (swapTop (rotateDown (rotateDown [abcd])))))))))))))))))))))))))))))) ≡ 𝕃→𝑳 [dcba]
-- test₁-raw₅ = {!refl!}
--  
-- -- memory conservative
-- test₁-raw₅-simpler : 𝕃→𝑳 (rotateDown (rotateDown (swapTop (rotateDown (rotateDown (rotateDown (swapTop (rotateDown (swapTop (rotateDown (rotateDown (swapTop (rotateDown (swapTop (rotateDown (swapTop (rotateDown (rotateDown [abcd])))))))))))))))))) ≡ 𝕃→𝑳 [dcba]
-- test₁-raw₅-simpler = refl

-- -- memory hog
-- test-rotateDown₂₄ : 𝕃→𝑳 (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown [abcd])))))))))))))))))))))))) ≡ 𝕃→𝑳 [abcd]
-- test-rotateDown₂₄ = {!refl!}

-- -- memory conservative
-- test-rotateDown₂₀ : 𝕃→𝑳 (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown (rotateDown [abcd])))))))))))))))))))) ≡ 𝕃→𝑳 [abcd]
-- test-rotateDown₂₀ = refl

-- test₂-6-5 : (rotateDown ∘ rotateDown ∘ rotateDown ∘ swapTop ∘ rotateDown $ [abcd]) ≡ [dcba]
-- test₂-6-5 = {!refl!} -- C-u C-u C-c C-.  : TODO this is getting very big

-- -- TODO the type takes a long time to typecheck...
-- {-
-- test₂-7-5 : 𝕃→𝑳 (rotateDown ∘ rotateDown ∘ rotateDown ∘ rotateDown ∘
--                  rotateDown ∘ rotateDown ∘ rotateDown ∘ rotateDown ∘
--                  rotateDown ∘ rotateDown ∘ rotateDown ∘ rotateDown ∘
--                  rotateDown ∘ rotateDown ∘ rotateDown ∘ rotateDown ∘
--                  rotateDown ∘ rotateDown ∘ rotateDown ∘ rotateDown ∘
--                  rotateDown ∘ rotateDown ∘ rotateDown ∘ rotateDown $
--                  [abcd]) ≡ 𝕃→𝑳 [abcd]
-- test₂-7-5 = {!refl!}
-- -}

-- -- ...but here, only the term is slow to typecheck
-- test₂-7-5' : 𝕃→𝑳 (rotateDown ( rotateDown ( rotateDown ( rotateDown (
--                   rotateDown ( rotateDown ( rotateDown ( rotateDown (
--                   rotateDown ( rotateDown ( rotateDown ( rotateDown (
--                   rotateDown ( rotateDown ( rotateDown ( rotateDown (
--                   rotateDown ( rotateDown ( rotateDown ( rotateDown (
--                   rotateDown ( rotateDown ( rotateDown ( rotateDown (
--                   [abcd]))))))))))))))))))))))))) ≡ 𝕃→𝑳 [abcd]
-- test₂-7-5' = refl -- C-u C-u C-c C-.  : TODO this is getting very big


-- test₃ : 𝕃→𝑳 (rotateDownBy 48 [abc]) ≡ 𝕃→𝑳 [abc]
-- test₃ = refl

-- -- time hogging, not memory hogging
-- test₄ : 𝕃→𝑳 (rotateDownBy 48 [ab]) ≡ 𝕃→𝑳 [ab]
-- test₄ = refl
