module Oscar.Prelude where

open import Agda.Primitive
     using ( Level
           )
  renaming ( _⊔_ to _⊔ₗ_
           ; lsuc to 𝟙+ₗ
           ; lzero to 𝟘ₗ
           )
     public

open import Relation.Binary public
     using ( IsDecEquivalence
           ; DecTotalOrder
           ; IsDecTotalOrder
           )
open import Agda.Builtin.Equality public
     using ( _≡_
           ; refl
           )

open import Data.Nat.Base public
     using ( ℕ
           ; _+_
           ; _*_
           )
  renaming ( suc to 𝟙+ )

open import Data.Nat public
     using ( decTotalOrder
           )

open import Relation.Binary.Core public
     using ( _≢_
           )
     
open import Relation.Nullary public
     using ( ¬_
           )

open import Data.Product public
     using ( Σ
           ; _,_
           ; ∃
           ; _×_ )
  renaming ( proj₁ to ↙
           ; proj₂ to ↘
           )

open import Data.Sum public
     using ( _⊎_
           ; [_,_]
           ; [_,_]′
           )
  renaming ( inj₁ to ↖
           ; inj₂ to ↗
           )

open import Relation.Nullary public
     using ( Dec
           ; yes
           ; no
           )

open import Function public
     using ( case_of_
           ; id
           )

open import Function public
     using ( _$_
           ; _∘_
           ; flip
           )

open import Data.Empty public
     using ( ⊥-elim
           )

open import Relation.Nullary.Negation public
     using ( contradiction
           ; decidable-stable
           )

open import Agda.Builtin.List public
     using ( List
           ; []
           ; _∷_
           )
           
open import Relation.Binary.PropositionalEquality.Core public
     using ( trans
           )
