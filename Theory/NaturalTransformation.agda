
module Theory.NaturalTransformation where

-- Stdlib
open import Level
open import Function hiding ( _∘_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

-- Local
open import Utilities
open import Theory.Category
open import Theory.Functor

open Category
open Functor

-------------------------------------------------------------------------------
-- Definition of Natural Transformations
-------------------------------------------------------------------------------
record NaturalTransformation {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                             (F : Functor C D) (G : Functor C D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  constructor naturalTransformation
  field
    η : (x : Obj C) → Hom D ([ F ]₀ x) ([ G ]₀ x)
    
    natural : {a b : Obj C} {f : Hom C a b} 
            → ( _∘_ D ([ G ]₁ f) (η a) ) ≡ ( _∘_ D (η b) ([ F ]₁ f) )
            -- G₁ f ∘ η ≡ η ∘ F₁ f

η⟨_⟩_ = NaturalTransformation.η

-------------------------------------------------------------------------------
-- The Identity Natural Transformation
-------------------------------------------------------------------------------
idNaturalTransformation : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                        → (F : Functor C D) → NaturalTransformation F F
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
                          → NaturalTransformation G H → NaturalTransformation F G
                          → NaturalTransformation F H
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

-------------------------------------------------------------------------------
-- Propositional Equality of Natural Transformations
-------------------------------------------------------------------------------

propEqNatTrans : {Cℓ₀ Cℓ₁ Dℓ₀ Dℓ₁ : Level} {C : Category {Cℓ₀} {Cℓ₁}} {D : Category {Dℓ₀} {Dℓ₁}} 
               → {F₀ G₀ F₁ G₁ : Functor C D}
               → {η₀ : (x : Obj C) → Hom D ([ F₀ ]₀ x) ([ G₀ ]₀ x)}
               → {η₁ : (x : Obj C) → Hom D ([ F₁ ]₀ x) ([ G₁ ]₀ x)}
               → {nat₀ : {a b : Obj C} {f : Hom C a b} → ( _∘_ D ([ G₀ ]₁ f) (η₀ a) ) ≡ ( _∘_ D (η₀ b) ([ F₀ ]₁ f) )}
               → {nat₁ : {a b : Obj C} {f : Hom C a b} → ( _∘_ D ([ G₁ ]₁ f) (η₁ a) ) ≡ ( _∘_ D (η₁ b) ([ F₁ ]₁ f) )}
               → (eq₀ : F₀ ≡ F₁)
               → (eq₁ : G₀ ≡ G₁)
               → (eq₂ : subst₂ (λ F G → (x : Obj C) → Hom D ([ F ]₀ x) ([ G ]₀ x)) eq₀ eq₁ η₀ ≡ η₁)
               → subst₂ (λ F G → NaturalTransformation F G) eq₀ eq₁ (naturalTransformation {F = F₀} {G = G₀} η₀ nat₀) 
               ≡ naturalTransformation {F = F₁} {G = G₁} η₁ nat₁
propEqNatTrans {nat₀ = nat₀} {nat₁} refl refl refl with p
  where
    p = funExtImplicit 
          (λ a → funExtImplicit 
          (λ b → funExtImplicit 
          (λ f → proof-irrelevance (nat₀ {a} {b} {f}) (nat₁ {a} {b} {f})
          ) ) )
propEqNatTrans {F₀ = functor F₀ F₁ idF distF} {functor G₀ G₁ idG distG} {functor .F₀ .F₁ .idF .distF} {functor .G₀ .G₁ .idG .distG} refl refl refl | refl = refl

-------------------------------------------------------------------------------
-- Category of Functors and Natural Transformations
-------------------------------------------------------------------------------

functorNatTransCategory : {Cℓ₀ Cℓ₁ Dℓ₀ Dℓ₁ : Level} 
                        → Category {Cℓ₀} {Cℓ₁} → Category {Dℓ₀} {Dℓ₁} → Category
functorNatTransCategory C D = record
  { Obj = Functor C D
  ; Hom = NaturalTransformation {C = C} {D}
  ; _∘_ = λ {F} {G} {H} → ⟨_⟩∘⟨_⟩ {C = C} {D} {F} {G} {H}
  ; id = λ {F} → Id⟨ F ⟩
  ; assoc = propEqNatTrans refl refl $ funExt $ λ _ → assoc D
  ; idL = propEqNatTrans refl refl $ funExt $ λ _ → idL D
  ; idR = propEqNatTrans refl refl $ funExt $ λ _ → idR D
  }
