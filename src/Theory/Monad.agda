
module Theory.Monad where

-- Stdlib
open import Level
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

-- Local
open import Congruence
open import Extensionality
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation

-------------------------------------------------------------------------------
-- Definition of Monads
-------------------------------------------------------------------------------
record Monad {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} (M : Functor C C) : Set (ℓC₀ ⊔ ℓC₁) where
  constructor monad
  
  open Category
  private
    _∘C_ = _∘_ C
  
  field
    η : NaturalTransformation Id[ C ]     M
    μ : NaturalTransformation [ M ]∘[ M ] M
  
  field
    μ-coher : {x : Obj C}
            → η⟨ μ ⟩ x ∘C [ M ]₁ (η⟨ μ ⟩ x) ≡ η⟨ μ ⟩ x ∘C η⟨ μ ⟩ ([ M ]₀ x)
            -- μ ∘ T₁μ ≡ μ ∘ μT₀

    η-left-coher : {x : Obj C}
                 → η⟨ μ ⟩ x ∘C [ M ]₁ (η⟨ η ⟩ x) ≡ η⟨ Id⟨ M ⟩ ⟩ x
                 -- μ ∘ Tη ≡ 1ₜ
    
    η-right-coher : {x : Obj C}
                  → η⟨ μ ⟩ x ∘C η⟨ η ⟩ ([ M ]₀ x) ≡ η⟨ Id⟨ M ⟩ ⟩ x
                  -- μ ∘ ηT ≡ 1ₜ

-------------------------------------------------------------------------------
-- Equality of Natural Transformations
-------------------------------------------------------------------------------

private
  module Equality {Cℓ₀ Cℓ₁ : Level} {C : Category {Cℓ₀} {Cℓ₁}} {M : Functor C C} where
    open Category C
     
    monad-eq : {η₀ : NaturalTransformation Id[ C ] M}
             → {η₁ : NaturalTransformation Id[ C ] M}
             → {μ₀ : NaturalTransformation [ M ]∘[ M ] M}
             → {μ₁ : NaturalTransformation [ M ]∘[ M ] M}
             → {μ-coher₀ : {x : Obj} → η⟨ μ₀ ⟩ x ∘ [ M ]₁ (η⟨ μ₀ ⟩ x) ≡ η⟨ μ₀ ⟩ x ∘ η⟨ μ₀ ⟩ ([ M ]₀ x)}
             → {μ-coher₁ : {x : Obj} → η⟨ μ₁ ⟩ x ∘ [ M ]₁ (η⟨ μ₁ ⟩ x) ≡ η⟨ μ₁ ⟩ x ∘ η⟨ μ₁ ⟩ ([ M ]₀ x)}
             → {η-left-coher₀ : {x : Obj} → η⟨ μ₀ ⟩ x ∘ [ M ]₁ (η⟨ η₀ ⟩ x) ≡ η⟨ Id⟨ M ⟩ ⟩ x}
             → {η-left-coher₁ : {x : Obj} → η⟨ μ₁ ⟩ x ∘ [ M ]₁ (η⟨ η₁ ⟩ x) ≡ η⟨ Id⟨ M ⟩ ⟩ x}
             → {η-right-coher₀ : {x : Obj} → η⟨ μ₀ ⟩ x ∘ η⟨ η₀ ⟩ ([ M ]₀ x) ≡ η⟨ Id⟨ M ⟩ ⟩ x}
             → {η-right-coher₁ : {x : Obj} → η⟨ μ₁ ⟩ x ∘ η⟨ η₁ ⟩ ([ M ]₀ x) ≡ η⟨ Id⟨ M ⟩ ⟩ x}
             → η₀ ≡ η₁
             → μ₀ ≡ μ₁
             → monad {M = M} η₀ μ₀ μ-coher₀ η-left-coher₀ η-right-coher₀ ≡ monad {M = M} η₁ μ₁ μ-coher₁ η-left-coher₁ η-right-coher₁
    monad-eq {η₀ = η₀} {.η₀} {μ₀} {.μ₀} {μ-coher₀} {μ-coher₁} {η-left-coher₀} {η-left-coher₁} {η-right-coher₀} {η-right-coher₁} refl refl 
      = cong₃ (monad η₀ μ₀) 
              (implicit-fun-ext (λ x → proof-irrelevance μ-coher₀ μ-coher₁)) 
              (implicit-fun-ext (λ x → proof-irrelevance η-left-coher₀ η-left-coher₁))
              (implicit-fun-ext (λ x → proof-irrelevance η-right-coher₀ η-right-coher₁))

open Equality using ( monad-eq ) public

-------------------------------------------------------------------------------
-- The Identity Monad
-------------------------------------------------------------------------------
idMonad : {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} → Monad (Id[ C ])
idMonad {C = C} = record 
  { η = Id⟨ Id[ C ] ⟩
  ; μ = Id⟨ Id[ C ] ⟩
  ; μ-coher = refl
  ; η-left-coher = Category.right-id C
  ; η-right-coher = Category.left-id C
  }

