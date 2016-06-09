
module Theory.NaturalTransformation where

-- Stdlib
open import Level
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

-- Local
open import Theory.Category
open import Theory.Functor

open Category
open Functor

record NaturalTransformation {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                             (F : Functor C D) (G : Functor C D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  field
    η : (x : Obj C) → Hom D ([ F ]₀ x) ([ G ]₀ x)
    
    natural : {a b : Obj C} {f : Hom C a b} 
            →  _∘_ D ([ G ]₁ f) (η a) ≡ _∘_ D (η b) ([ F ]₁ f)
            -- G₁ f ∘ η ≡ η ∘ F₁ f
 
η⟨_⟩ : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {F G : Functor C D}
     → (N : NaturalTransformation F G) → (x : Obj C) → Hom D ([ F ]₀ x) ([ G ]₀ x)
η⟨ N ⟩ x = NaturalTransformation.η N x

idNaturalTransformation : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                        → (F : Functor C D) → NaturalTransformation F F
idNaturalTransformation {C = C} {D = D} F = record 
  { η = λ x → Category.id D
  ; natural = trans (idR D) (sym (idL D))
  }

Id⟨_⟩ : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
      → (F : Functor C D) → NaturalTransformation F F
Id⟨ F ⟩ = idNaturalTransformation F
