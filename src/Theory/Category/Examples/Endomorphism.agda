
-- Stdlib
open import Level

open import Relation.Binary.PropositionalEquality

open import Theory.Category.Definition

module Theory.Category.Examples.Endomorphism where 

-- Category that only contains the endomorphisms of the given category.
endomorphismCategory : {ℓ₀ ℓ₁ : Level} → Category {ℓ₀} {ℓ₁} → Category {ℓ₀} {ℓ₀ ⊔ ℓ₁}
endomorphismCategory {ℓ₀} {ℓ₁} C = record
  { Obj = Obj
  ; Hom = Hom
  ; _∘_ = λ {a} {b} {c} → _∘_ {a} {b} {c}
  ; id = λ {a} → id {a}
  ; assoc = assoc
  ; left-id = left-id
  ; right-id = right-id
  } where
    open import Data.Product
    
    Obj : Set ℓ₀
    Obj = Category.Obj C
    
    Hom : Obj → Obj → Set (ℓ₀ ⊔ ℓ₁)
    Hom a b = Category.Hom C a b × a ≡ b
    
    _∘C_ = Category._∘_ C
    
    _∘_ : {a b c : Obj} → Hom b c → Hom a b → Hom a c
    (f , refl) ∘ (g , refl) = f ∘C g , refl
    
    id : {a : Obj} → Hom a a
    id = Category.id C , refl

    assoc : {a b c d : Obj} {f : Hom a b} {g : Hom b c} {h : Hom c d} → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    assoc {f = f , refl} {g , refl} {h , refl} = cong (λ X → X , refl) (Category.assoc C {f = f} {g} {h})
    
    left-id : {a b : Obj} {f : Hom a b} → f ∘ id ≡ f
    left-id {f = f , refl} = cong (λ X → X , refl) (Category.left-id C {f = f})
    
    right-id : {a b : Obj} {f : Hom a b} → id ∘ f ≡ f
    right-id {f = f , refl} = cong (λ X → X , refl) (Category.right-id C {f = f})
