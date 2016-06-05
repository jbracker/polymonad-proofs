
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

record NaturalTransformation {ℓ : Level} 
                             {C D : Category {ℓ = ℓ}} 
                             (F : Functor C D) (G : Functor C D) : Set ℓ where
  field
    η : (x : Obj C) → Hom D ([ F ]₀ x) ([ G ]₀ x)
    
    natural : {a b : Obj C} {f : Hom C a b} 
            →  _∘_ D ([ G ]₁ f) (η a) ≡ _∘_ D (η b) ([ F ]₁ f)
 
η⟨_⟩ : ∀ {ℓ} {C D : Category {ℓ = ℓ}} {F G : Functor C D}
     → (N : NaturalTransformation F G) → (x : Obj C) → Hom D ([ F ]₀ x) ([ G ]₀ x)
η⟨ N ⟩ x = NaturalTransformation.η N x

idNaturalTransformation : {ℓ : Level} {C D : Category {ℓ = ℓ}}
                        → (F : Functor C D) → NaturalTransformation F F
idNaturalTransformation {C = C} {D = D} F = record 
  { η = λ x → Category.id D
  ; natural = trans (idR D) (sym (idL D))
  }

Id⟨_⟩ : {ℓ : Level} {C D : Category {ℓ = ℓ}} 
      → (F : Functor C D) → NaturalTransformation F F
Id⟨ F ⟩ = idNaturalTransformation F
