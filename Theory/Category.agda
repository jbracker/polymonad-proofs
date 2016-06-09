
module Theory.Category where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record Category {ℓ₀ ℓ₁ : Level} : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  field
    Obj : Set ℓ₀
    Hom : Obj → Obj → Set ℓ₁
    
    _∘_ : ∀ {a b c} → Hom b c → Hom a b → Hom a c
    id : ∀ {a} → Hom a a
    
    assoc : {a b c d : Obj} {f : Hom a b} {g : Hom b c} {h : Hom c d} 
          → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    idL : {a b : Obj} {f : Hom a b} → id ∘ f ≡ f
    idR : {a b : Obj} {f : Hom a b} → f ∘ id ≡ f

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
setCategory : {ℓ₀ : Level} → Category
setCategory {ℓ₀ = ℓ₀} = record
  { Obj = Set ℓ₀
  ; Hom = λ a b → (a → b)
  ; _∘_ = λ f g → f ∘F g
  ; id = idF
  ; assoc = refl
  ; idL = refl
  ; idR = refl
  }

