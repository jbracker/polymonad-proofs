
open import Level
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Relation.Binary.PropositionalEquality

open import Substitution
open import Congruence
open import Theory.Category

module Theory.Category.Isomorphism where

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
    isomorphism-eq {inv₀ = inv} {.inv} {left-id} {left-id'} {right-id} {right-id'} refl 
      = cong₂ (isomorphism inv) (proof-irrelevance left-id left-id') (proof-irrelevance right-id right-id')

open Equality using ( isomorphism-eq ) public

open Category
open Isomorphism

isoId : {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}} {a : Obj C} → Isomorphism C (id C {a})
isoId {C = C} {a} = isomorphism (id C {a}) (Category.left-id C) (Category.right-id C)

_∘Iso_ : {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}} {a b c : Obj C}
       → {f : Hom C b c} {g : Hom C a b} 
       → (Isomorphism C f) → Isomorphism C g → Isomorphism C (_∘_ C f g)
_∘Iso_ {ℓ₀} {ℓ₁} {C} {a} {b} {c} {f} {g} iso-f iso-g = isomorphism ((inv iso-g) ∘C (inv iso-f)) left-id' right-id'
  where
    _∘C_ = _∘_ C
    
    open ≡-Reasoning
    
    left-id' : (f ∘C g) ∘C (inv iso-g ∘C inv iso-f) ≡ id C
    left-id' = begin
      (f ∘C g) ∘C (inv iso-g ∘C inv iso-f) 
        ≡⟨ sym (assoc C) ⟩
      f ∘C (g ∘C (inv iso-g ∘C inv iso-f))
        ≡⟨ cong (_∘C_ f) (assoc C) ⟩
      f ∘C ((g ∘C inv iso-g) ∘C inv iso-f)
        ≡⟨ cong (λ P → f ∘C (P ∘C inv iso-f)) (Isomorphism.left-id iso-g) ⟩
      f ∘C (id C ∘C inv iso-f)
        ≡⟨ cong (_∘C_ f) (Category.right-id C) ⟩
      f ∘C inv iso-f
        ≡⟨ Isomorphism.left-id iso-f ⟩
      id C ∎
    
    right-id' : (inv iso-g ∘C inv iso-f) ∘C (f ∘C g) ≡ id C
    right-id' = begin
      (inv iso-g ∘C inv iso-f) ∘C (f ∘C g) 
        ≡⟨ sym (assoc C) ⟩
      inv iso-g ∘C (inv iso-f ∘C (f ∘C g))
        ≡⟨ cong (_∘C_ (inv iso-g)) (assoc C) ⟩
      inv iso-g ∘C ((inv iso-f ∘C f) ∘C g)
        ≡⟨ cong (λ P → inv iso-g ∘C (P ∘C g)) (Isomorphism.right-id iso-f) ⟩
      inv iso-g ∘C (id C ∘C g)
        ≡⟨ cong (_∘C_ (inv iso-g)) (Category.right-id C) ⟩
      inv iso-g ∘C g
        ≡⟨ Isomorphism.right-id iso-g ⟩
      id C ∎
