
-- Stdlib
open import Level
open import Function renaming ( id to idF ; _∘_ to _∘F_ )

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; proof-irrelevance to het-proof-irrelevance )
open ≡-Reasoning 

-- Local
open import Congruence
open import Extensionality
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

module Theory.Monad.Definition where

open NaturalTransformation renaming ( η to nat-η )

-------------------------------------------------------------------------------
-- Definition of Monads
-------------------------------------------------------------------------------
record Monad {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} (M : Functor C C) : Set (ℓC₀ ⊔ ℓC₁) where
  constructor monad
  
  open Category
  open NaturalTransformation renaming ( η to nat-η )
  private
    _∘C_ = _∘_ C
  
  field
    η : NaturalTransformation Id[ C ]     M
    μ : NaturalTransformation [ M ]∘[ M ] M
  
  field
    μ-coher : {x : Obj C}
            → nat-η μ x ∘C [ M ]₁ (nat-η μ x) ≡ nat-η μ x ∘C nat-η μ ([ M ]₀ x)
            -- μ ∘ T₁μ ≡ μ ∘ μT₀

    η-left-coher : {x : Obj C}
                 → nat-η μ x ∘C [ M ]₁ (nat-η η x) ≡ nat-η Id⟨ M ⟩ x
                 -- μ ∘ Tη ≡ 1ₜ
    
    η-right-coher : {x : Obj C}
                  → nat-η μ x ∘C nat-η η ([ M ]₀ x) ≡ nat-η Id⟨ M ⟩ x
                  -- μ ∘ ηT ≡ 1ₜ

  functor-connection : {α β : Obj C} → (f : Hom C α β) → [ M ]₁ f ≡ nat-η μ β ∘C ([ M ]₁ (nat-η η β ∘C f))
  functor-connection {α} {β} f = begin
    [ M ]₁ f
      ≡⟨ sym $ right-id C ⟩
    nat-η Id⟨ M ⟩ β ∘C [ M ]₁ f
      ≡⟨ cong (λ X → X ∘C [ M ]₁ f) $ sym $ η-left-coher ⟩
    (nat-η μ β ∘C [ M ]₁ (nat-η η β)) ∘C [ M ]₁ f
      ≡⟨ sym $ assoc C ⟩
    nat-η μ β ∘C ([ M ]₁ (nat-η η β) ∘C [ M ]₁ f)
      ≡⟨ cong (λ X → nat-η μ β ∘C X) $ sym $ Functor.compose M ⟩
    nat-η μ β ∘C ([ M ]₁ (nat-η η β ∘C f)) ∎

-------------------------------------------------------------------------------
-- Equality of Natural Transformations
-------------------------------------------------------------------------------

private
  module Equality {Cℓ₀ Cℓ₁ : Level} {C : Category {Cℓ₀} {Cℓ₁}} {M : Functor C C} where
    open Category C
     
    abstract
      monad-eq : {η₀ : NaturalTransformation Id[ C ] M}
               → {η₁ : NaturalTransformation Id[ C ] M}
               → {μ₀ : NaturalTransformation [ M ]∘[ M ] M}
               → {μ₁ : NaturalTransformation [ M ]∘[ M ] M}
               → {μ-coher₀ : {x : Obj} → nat-η μ₀ x ∘ [ M ]₁ (nat-η μ₀ x) ≡ nat-η μ₀ x ∘ nat-η μ₀ ([ M ]₀ x)}
               → {μ-coher₁ : {x : Obj} → nat-η μ₁ x ∘ [ M ]₁ (nat-η μ₁ x) ≡ nat-η μ₁ x ∘ nat-η μ₁ ([ M ]₀ x)}
               → {η-left-coher₀ : {x : Obj} → nat-η μ₀ x ∘ [ M ]₁ (nat-η η₀ x) ≡ nat-η Id⟨ M ⟩ x}
               → {η-left-coher₁ : {x : Obj} → nat-η μ₁ x ∘ [ M ]₁ (nat-η η₁ x) ≡ nat-η Id⟨ M ⟩ x}
               → {η-right-coher₀ : {x : Obj} → nat-η μ₀ x ∘ nat-η η₀ ([ M ]₀ x) ≡ nat-η Id⟨ M ⟩ x}
               → {η-right-coher₁ : {x : Obj} → nat-η μ₁ x ∘ nat-η η₁ ([ M ]₀ x) ≡ nat-η Id⟨ M ⟩ x}
               → η₀ ≡ η₁
               → μ₀ ≡ μ₁
               → monad {M = M} η₀ μ₀ μ-coher₀ η-left-coher₀ η-right-coher₀ ≡ monad {M = M} η₁ μ₁ μ-coher₁ η-left-coher₁ η-right-coher₁
      monad-eq {η₀ = η₀} {.η₀} {μ₀} {.μ₀} {μ-coher₀} {μ-coher₁} {η-left-coher₀} {η-left-coher₁} {η-right-coher₀} {η-right-coher₁} refl refl 
        = cong₃ (monad η₀ μ₀) 
                (implicit-fun-ext (λ x → proof-irrelevance μ-coher₀ μ-coher₁)) 
                (implicit-fun-ext (λ x → proof-irrelevance η-left-coher₀ η-left-coher₁))
                (implicit-fun-ext (λ x → proof-irrelevance η-right-coher₀ η-right-coher₁))

      het-monad-eq : {M' : Functor C C}
                   → {η₀ : NaturalTransformation Id[ C ] M}
                   → {η₁ : NaturalTransformation Id[ C ] M'}
                   → {μ₀ : NaturalTransformation [ M ]∘[ M ] M}
                   → {μ₁ : NaturalTransformation [ M' ]∘[ M' ] M'}
                   → {μ-coher₀ : {x : Obj} → nat-η μ₀ x ∘ [ M ]₁ (nat-η μ₀ x) ≡ nat-η μ₀ x ∘ nat-η μ₀ ([ M ]₀ x)}
                   → {μ-coher₁ : {x : Obj} → nat-η μ₁ x ∘ [ M' ]₁ (nat-η μ₁ x) ≡ nat-η μ₁ x ∘ nat-η μ₁ ([ M' ]₀ x)}
                   → {η-left-coher₀ : {x : Obj} → nat-η μ₀ x ∘ [ M ]₁ (nat-η η₀ x) ≡ nat-η Id⟨ M ⟩ x}
                   → {η-left-coher₁ : {x : Obj} → nat-η μ₁ x ∘ [ M' ]₁ (nat-η η₁ x) ≡ nat-η Id⟨ M' ⟩ x}
                   → {η-right-coher₀ : {x : Obj} → nat-η μ₀ x ∘ nat-η η₀ ([ M ]₀ x) ≡ nat-η Id⟨ M ⟩ x}
                   → {η-right-coher₁ : {x : Obj} → nat-η μ₁ x ∘ nat-η η₁ ([ M' ]₀ x) ≡ nat-η Id⟨ M' ⟩ x}
                   → M ≡ M'
                   → η₀ ≅ η₁
                   → μ₀ ≅ μ₁
                   → monad {M = M} η₀ μ₀ μ-coher₀ η-left-coher₀ η-right-coher₀ ≅ monad {M = M'} η₁ μ₁ μ-coher₁ η-left-coher₁ η-right-coher₁
      het-monad-eq {.M} {η₀ = η} {.η} {μ} {.μ} {μ-coher₀} {μ-coher₁} {η-left-coher₀} {η-left-coher₁} {η-right-coher₀} {η-right-coher₁} refl hrefl hrefl
        = ≡-to-≅ $ cong₃ (monad η μ) 
                (implicit-fun-ext (λ x → proof-irrelevance μ-coher₀ μ-coher₁)) 
                (implicit-fun-ext (λ x → proof-irrelevance η-left-coher₀ η-left-coher₁))
                (implicit-fun-ext (λ x → proof-irrelevance η-right-coher₀ η-right-coher₁))

open Equality using ( monad-eq ; het-monad-eq ) public

-------------------------------------------------------------------------------
-- The Identity Monad
-------------------------------------------------------------------------------
idMonad : {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} → Monad (Id[ C ])
idMonad {C = C} = record 
  { η = Id⟨ Id[ C ] ⟩
  ; μ = naturalTransformation (λ x → Category.id C {x}) μ-nat
  ; μ-coher = refl
  ; η-left-coher = Category.right-id C
  ; η-right-coher = Category.left-id C
  } where
    open Category
    _∘C_ = _∘_ C
    
    abstract
      μ-nat : {a b : Obj C} {f : Hom C a b}
            → ([ Id[ C ] ]₁ f) ∘C (Category.id C) ≡ (Category.id C) ∘C ([ [ Id[ C ] ]∘[ Id[ C ] ] ]₁ f)
      μ-nat {a} {b} {f} = begin
        ([ Id[ C ] ]₁ f) ∘C (Category.id C) 
          ≡⟨ left-id C ⟩
        ([ Id[ C ] ]₁ f)
          ≡⟨ refl ⟩
        f
          ≡⟨ refl ⟩
        ([ [ Id[ C ] ]∘[ Id[ C ] ] ]₁ f)
          ≡⟨ sym (right-id C) ⟩
        (Category.id C) ∘C ([ [ Id[ C ] ]∘[ Id[ C ] ] ]₁ f) ∎
