
module Theory.Natural.Transformation.Whisker where

-- Stdlib
open import Level
open import Function hiding ( _∘_ ; id )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

-- Local
open import Utilities
open import Extensionality
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

open Category
open Functor 
open NaturalTransformation

-- Based on the slides: 
-- http://www.math.vanderbilt.edu/~tacl2013/coursematerials/SelingerTACL20132.pdf

-------------------------------------------------------------------------------
-- Left whiskering of natural transformations
-------------------------------------------------------------------------------

leftWhiskerNatTrans : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
                    → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}}
                    → {G H : Functor D E} 
                    → (α : NaturalTransformation G H) 
                    → (F : Functor C D)
                    → NaturalTransformation [ G ]∘[ F ] [ H ]∘[ F ]
leftWhiskerNatTrans {C = C} {D} {E} {G} {H} α F = record 
  { η = λ x → η α ([ F ]₀ x)
  ; natural = natural α
  }

⟨_⟩∘[_] = leftWhiskerNatTrans

-------------------------------------------------------------------------------
-- Right whiskering of natural transformations
-------------------------------------------------------------------------------

rightWhiskerNatTrans : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
                     → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}}
                     → {G H : Functor C D} 
                     → (F : Functor D E)
                     → (α : NaturalTransformation G H) 
                     → NaturalTransformation [ F ]∘[ G ] [ F ]∘[ H ]
rightWhiskerNatTrans {C = C} {D} {E} {G} {H} F α = record 
  { η = λ x → [ F ]₁ (η α x)
  ; natural = λ {a} {b} {f} → begin
      [ F ]₁ ([ H ]₁ f) ∘E ([ F ]₁ (η α a)) 
        ≡⟨ sym (compose F) ⟩
      [ F ]₁ ([ H ]₁ f ∘D η α a)
        ≡⟨ cong (F₁ F) (natural α) ⟩
      [ F ]₁ (η α b ∘D [ G ]₁ f)
        ≡⟨ compose F ⟩
      [ F ]₁ (η α b) ∘E [ F ]₁ ([ G ]₁ f) ∎
  } where _∘E_ = _∘_ E ; _∘D_ = _∘_ D

[_]∘⟨_⟩ = rightWhiskerNatTrans

-------------------------------------------------------------------------------
-- Laws about whiskering
-------------------------------------------------------------------------------

abstract
  rightWhiskerDist 
    : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
    → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}}
    → {F G H : Functor C D} 
    → (K : Functor D E)
    → (α : NaturalTransformation F G)
    → (β : NaturalTransformation G H)
    → [ K ]∘⟨ ⟨ β ⟩∘ᵥ⟨ α ⟩ ⟩ ≡ ⟨ [ K ]∘⟨ β ⟩ ⟩∘ᵥ⟨ [ K ]∘⟨ α ⟩ ⟩
  rightWhiskerDist {C = C} {D} {E} {F} {G} {H} K α β =
    natural-transformation-eq $ fun-ext $ λ (x : Obj C) → begin
      η [ K ]∘⟨ ⟨ β ⟩∘ᵥ⟨ α ⟩ ⟩ x 
        ≡⟨ refl ⟩
      [ K ]₁ (η β x ∘D η α x)
        ≡⟨ compose K ⟩
      [ K ]₁ (η β x) ∘E [ K ]₁ (η α x)
        ≡⟨ refl ⟩
      η ⟨ [ K ]∘⟨ β ⟩ ⟩∘ᵥ⟨ [ K ]∘⟨ α ⟩ ⟩ x ∎
    where _∘E_ = _∘_ E ; _∘D_ = _∘_ D

abstract
  leftWhiskerDist 
    : {ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
    → {B : Category {ℓB₀} {ℓB₁}} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} 
    → {F G H : Functor C D} 
    → (K : Functor B C)
    → (α : NaturalTransformation F G)
    → (β : NaturalTransformation G H)
    → ⟨ ⟨ β ⟩∘ᵥ⟨ α ⟩ ⟩∘[ K ] ≡ ⟨ ⟨ β ⟩∘[ K ] ⟩∘ᵥ⟨ ⟨ α ⟩∘[ K ] ⟩
  leftWhiskerDist {B = B} K α β =
    natural-transformation-eq $ fun-ext $ λ (x : Obj B) → refl

abstract
  leftWhiskerId₁
    : {ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
    → {B : Category {ℓB₀} {ℓB₁}} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} 
    → {F : Functor C D} 
    → (K : Functor B C)
    → ⟨ Id⟨ F ⟩ ⟩∘[ K ] ≡ Id⟨ [ F ]∘[ K ] ⟩
  leftWhiskerId₁ {B = B} K = 
    natural-transformation-eq $ fun-ext $ λ (x : Obj B) → refl

abstract
  leftWhiskerId₂
    : {ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
    → {B : Category {ℓB₀} {ℓB₁}} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} 
    → {F G : Functor C D} 
    → (K : Functor B C)
    → (α : NaturalTransformation F G)
    → ⟨ α ⟩∘ₕ⟨ Id⟨ K ⟩ ⟩ ≡ ⟨ α ⟩∘[ K ]
  leftWhiskerId₂ {B = B} {C} {D} {F} {G} K α = 
    natural-transformation-eq $ fun-ext $ λ (x : Obj B) → begin
      η ⟨ α ⟩∘ₕ⟨ Id⟨ K ⟩ ⟩ x 
        ≡⟨ refl ⟩
      η α ([ K ]₀ x) ∘D [ F ]₁ (Category.id C) 
        ≡⟨ cong (λ X → η α ([ K ]₀ x) ∘D X) (Functor.id F) ⟩
      η α ([ K ]₀ x) ∘D Category.id D 
        ≡⟨ left-id D ⟩
      η α ([ K ]₀ x)
        ≡⟨ refl ⟩
      η ⟨ α ⟩∘[ K ] x ∎
    where _∘D_ = _∘_ D

abstract
  rightWhiskerId₁ 
    : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
    → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}} 
    → {F : Functor C D} 
    → (K : Functor D E)
    → [ K ]∘⟨ Id⟨ F ⟩ ⟩ ≡ Id⟨ [ K ]∘[ F ] ⟩
  rightWhiskerId₁ {C = C} K = 
    natural-transformation-eq $ fun-ext $ λ (x : Obj C) → Functor.id K

abstract
  rightWhiskerId₂
    : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
    → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}} 
    → {F G : Functor C D} 
    → (K : Functor D E)
    → (α : NaturalTransformation F G)
    → ⟨ Id⟨ K ⟩ ⟩∘ₕ⟨ α ⟩ ≡ [ K ]∘⟨ α ⟩
  rightWhiskerId₂ {C = C} {D} {E} {F} {G} K α = 
    natural-transformation-eq $ fun-ext $ λ (x : Obj C) → right-id E

abstract
  whiskerCompositionHorzEq 
    : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
    → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}}
    → {F G : Functor C D}
    → {H K : Functor D E}
    → (α : NaturalTransformation F G)
    → (β : NaturalTransformation H K)
    → ⟨ [ K ]∘⟨ α ⟩ ⟩∘ᵥ⟨ ⟨ β ⟩∘[ F ] ⟩ ≡ ⟨ ⟨ β ⟩∘[ G ] ⟩∘ᵥ⟨ [ H ]∘⟨ α ⟩ ⟩
  whiskerCompositionHorzEq {C = C} {D} {E} {F} {G} {H} {K} α β = 
    natural-transformation-eq $ fun-ext $ λ (x : Obj C) → begin
      η ⟨ [ K ]∘⟨ α ⟩ ⟩∘ᵥ⟨ ⟨ β ⟩∘[ F ] ⟩ x
        ≡⟨ refl ⟩ 
      [ K ]₁ (η α x) ∘E η β ([ F ]₀ x)
        ≡⟨ natural β ⟩ 
      η β ([ G ]₀ x) ∘E [ H ]₁ (η α x)
        ≡⟨ refl ⟩ 
      η ⟨ ⟨ β ⟩∘[ G ] ⟩∘ᵥ⟨ [ H ]∘⟨ α ⟩ ⟩ x ∎
    where _∘E_ = _∘_ E
