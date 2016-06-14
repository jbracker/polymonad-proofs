
module Theory.Category.Examples where 

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Theory.Category
open import Theory.Functor

-- The unit category with exactly one element and one morphism.
unitCategory : {ℓ₀ ℓ₁ : Level} → Category {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁}
unitCategory = record
  { Obj = Lift ⊤
  ; Hom = λ _ _ → Lift ⊤
  ; _∘_ = λ _ _ → lift tt
  ; id = lift tt
  ; assoc = refl
  ; idL = refl
  ; idR = refl
  }

-- Category of sets and functions.
setCategory : {ℓ₀ : Level} → Category {ℓ₀ = lsuc ℓ₀}
setCategory {ℓ₀ = ℓ₀} = record
  { Obj = Set ℓ₀
  ; Hom = λ a b → (a → b)
  ; _∘_ = λ f g → f ∘F g
  ; id = idF
  ; assoc = refl
  ; idL = refl
  ; idR = refl
  }

{-
-- Category of categories and functors.
catCategory : {ℓC ℓF ℓ₀ ℓ₁ : Level} 
            → (Cats : Set ℓC) → (catOf : Cats → Category {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁}) 
            → (Funcs : (C : Cats) → (D : Cats) → ∃ λ (Fs : Set ℓF) → ((f : Fs) → Functor (catOf C) (catOf D)) ) 
            → Category {ℓ₀ = ℓC} {ℓ₁ = ℓ₁ ⊔ (ℓ₀ ⊔ lsuc ℓF)}
catCategory Cats catOf Funcs = record
  { Obj = Cats
  ; Hom = λ C D → {!Funcs C D!}
  ; _∘_ = {!!}
  ; id = {!!}
  ; assoc = {!!}
  ; idL = {!!}
  ; idR = {!!}
  }
-}
