
open import Level
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Relation.Binary.PropositionalEquality

open import Substitution
open import Congruence
open import Theory.Category

module Theory.Isomorphism where


open Category hiding ( idL ; idR )

-------------------------------------------------------------------------------
-- Definition of what is means for a morphism to be isomorphic with a 2-sided inverse.
-------------------------------------------------------------------------------
record Isomorphism {ℓ₀ ℓ₁ : Level} (C : Category {ℓ₀} {ℓ₁}) {a b : Obj C} (f : Hom C a b) : Set ℓ₁ where
  constructor isomorphism
  
  private
    _∘C_ = _∘_ C
  
  field
    f⁻¹ : Hom C b a
    
    idL : f ∘C f⁻¹ ≡ id C {b}

    idR : f⁻¹ ∘C f ≡ id C {a}

  inv : Hom C b a
  inv = f⁻¹

-------------------------------------------------------------------------------
-- Equality of isomorphisms
-------------------------------------------------------------------------------
isomorphism-eq : {ℓ₀ ℓ₁ : Level} 
               → {C : Category {ℓ₀} {ℓ₁}}
               → {a b : Obj C}
               → {f : Hom C a b}
               → {inv : Hom C b a} {inv' : Hom C b a}
               → {idL : _∘_ C f inv ≡ id C {b}} → {idL' : _∘_ C f inv' ≡ id C {b}}
               → {idR : _∘_ C inv f ≡ id C {a}} → {idR' : _∘_ C inv' f ≡ id C {a}}
               → inv ≡ inv'
               → isomorphism {C = C} inv idL idR ≡ isomorphism inv' idL' idR'
isomorphism-eq {inv = inv} {.inv} {idL} {idL'} {idR} {idR'} refl 
  = cong₂ (isomorphism inv) (proof-irrelevance idL idL') (proof-irrelevance idR idR')
