
open import Level
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Relation.Binary.PropositionalEquality

open import Substitution
open import Congruence
open import Theory.Category

module Theory.Isomorphism where

open Category using ( Obj ; Hom )

-------------------------------------------------------------------------------
-- Definition of what is means for a morphism to be isomorphic with a 2-sided inverse.
-------------------------------------------------------------------------------
record Isomorphism {ℓ₀ ℓ₁ : Level} (C : Category {ℓ₀} {ℓ₁}) {a b : Obj C} (f : Hom C a b) : Set ℓ₁ where
  constructor isomorphism
  
  open Category C hiding ( left-id ; right-id ; Obj ; Hom )
  
  field
    f⁻¹ : Hom C b a
    
    left-id : f ∘ f⁻¹ ≡ id {b}

    right-id : f⁻¹ ∘ f ≡ id {a}

  inv : Hom C b a
  inv = f⁻¹

-------------------------------------------------------------------------------
-- Equality of isomorphisms
-------------------------------------------------------------------------------

private
  module Equality {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}} {a b : Obj C} {f : Hom C a b} where
    open Category C hiding ( Obj ; Hom )
  
    isomorphism-eq : {inv₀ : Hom C b a} 
                   → {inv₁ : Hom C b a}
                   → {left-id₀ : f ∘ inv₀ ≡ id {b}} 
                   → {left-id₁ : f ∘ inv₁ ≡ id {b}}
                   → {right-id₀ : inv₀ ∘ f ≡ id {a}}
                   → {right-id₁ : inv₁ ∘ f ≡ id {a}}
                   → inv₀ ≡ inv₁
                   → isomorphism {C = C} inv₀ left-id₀ right-id₀ ≡ isomorphism inv₁ left-id₁ right-id₁
    isomorphism-eq {inv₀ = inv} {.inv} {idL} {idL'} {idR} {idR'} refl 
      = cong₂ (isomorphism inv) (proof-irrelevance idL idL') (proof-irrelevance idR idR')

open Equality using ( isomorphism-eq ) public
