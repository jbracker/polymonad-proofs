
module Theory.NaturalTransformation where

-- Stdlib
open import Level
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

-- Local
open import Theory.Category
open import Theory.Functor

open Category
open Functor

-------------------------------------------------------------------------------
-- Definition of Natural Transformations
-------------------------------------------------------------------------------
record NaturalTransformation {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                             (_∼_ : ∀ {a b} → Rel (Hom D a b) ℓD₁) (F : Functor C D) (G : Functor C D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  field
    η : (x : Obj C) → Hom D ([ F ]₀ x) ([ G ]₀ x)
    
    natural : {a b : Obj C} {f : Hom C a b} 
            → ( _∘_ D ([ G ]₁ f) (η a) ) ∼ ( _∘_ D (η b) ([ F ]₁ f) )
            -- G₁ f ∘ η ≡ η ∘ F₁ f

η⟨_⟩_ = NaturalTransformation.η

-------------------------------------------------------------------------------
-- The Identity Natural Transformation
-------------------------------------------------------------------------------
idNaturalTransformation : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                        → (F : Functor C D) → NaturalTransformation _≡_ F F
idNaturalTransformation {C = C} {D = D} F = record 
  { η = λ x → Category.id D
  ; natural = trans (idR D) (sym (idL D))
  }

Id⟨_⟩ = idNaturalTransformation

-------------------------------------------------------------------------------
-- Composition of Natural Transformations
-------------------------------------------------------------------------------

compNaturalTransformation : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                          → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                          → {F G H : Functor C D}
                          → NaturalTransformation _≡_ G H → NaturalTransformation _≡_ F G
                          → NaturalTransformation _≡_ F H
compNaturalTransformation {C = C} {D} {F} {G} {H} α β =  record 
  { η = η 
  ; natural = natural
  } where
    _∘D_ = Category._∘_ D
    ηα = NaturalTransformation.η α
    ηβ = NaturalTransformation.η β
    
    η :  (a : Category.Obj C) → Category.Hom D ([ F ]₀ a) ([ H ]₀ a)
    η a = ηα a ∘D ηβ a
    
    natural : {a b : Category.Obj C} {f : Category.Hom C a b} → ([ H ]₁ f) ∘D (η a) ≡ (η b) ∘D ([ F ]₁ f)
    natural {a} {b} {f} = begin
      ([ H ]₁ f) ∘D (η a) 
        ≡⟨ refl ⟩
      ([ H ]₁ f) ∘D (ηα a ∘D ηβ a) 
        ≡⟨ Category.assoc D ⟩
      (([ H ]₁ f) ∘D ηα a) ∘D ηβ a 
        ≡⟨ cong (λ X → X ∘D ηβ a) (NaturalTransformation.natural α) ⟩
      (ηα b ∘D ([ G ]₁ f)) ∘D ηβ a 
        ≡⟨ sym (Category.assoc D) ⟩
      ηα b ∘D (([ G ]₁ f) ∘D ηβ a)
        ≡⟨ cong (λ X → ηα b ∘D X) (NaturalTransformation.natural β) ⟩
      ηα b ∘D (ηβ b ∘D ([ F ]₁ f))
        ≡⟨ Category.assoc D ⟩
      (ηα b ∘D ηβ b) ∘D ([ F ]₁ f)
        ≡⟨ refl ⟩
      (η b) ∘D ([ F ]₁ f) ∎

⟨_⟩∘⟨_⟩ = compNaturalTransformation

