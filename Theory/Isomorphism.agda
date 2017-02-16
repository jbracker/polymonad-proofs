
open import Level
open import Relation.Binary.PropositionalEquality

open import Theory.Category

module Theory.Isomorphism where


open Category hiding ( idL ; idR )

-- Definition of what is means for a morphism to be isomorphic with a 2-sided inverse.
record Isomorphism {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}} {a b : Obj C} (f : Hom C a b) : Set ℓ₁ where
  constructor isomorphism
  
  private
    _∘C_ = _∘_ C
  
  field
    f⁻¹ : Hom C b a
    
    idL : f ∘C f⁻¹ ≡ id C {b}

    idR : f⁻¹ ∘C f ≡ id C {a}

  inv : Hom C b a
  inv = f⁻¹
