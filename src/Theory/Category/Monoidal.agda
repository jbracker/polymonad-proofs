 
module Theory.Category.Monoidal where

open import Level renaming ( zero to lzero ; suc to lsuc )
open import Data.Product renaming ( _,_ to _,'_ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.HeterogeneousEquality using ( _≅_ )

open import Theory.Triple
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalIsomorphism
open import Theory.Examples.Functor

module FunctorApplication {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} where
  
  open Category renaming ( id to idC )
  open Functor renaming ( id to idF )
  
  private
    _∘CCC_ = _∘_ (C ×C C ×C C)
    _∘C_ = _∘_ C
  
  open Theory.Examples.Functor.TripleAssociation
  open Theory.Examples.Functor.BiFunctorAssociation
  
  -- ((_ ⊗ _) ⊗ _) ⇒ _
  leftAssociator : Functor (C ×C C) C → Functor (C ×C C ×C C) C
  leftAssociator F = [ biAssocFunctorL F F ]∘[ assocFunctorL ]
  
  -- (_ ⊗ (_ ⊗ _)) ⇒ _
  rightAssociator : Functor (C ×C C) C → Functor (C ×C C ×C C) C 
  rightAssociator F = [ biAssocFunctorR F F ]∘[ assocFunctorR ]
  
  -- (1 ⊗ _) ⇒ _
  leftUnitor : Obj C → Functor (C ×C C) C → Functor C C
  leftUnitor e F = functor G₀ G₁ idG composeG
    where
      G₀ : Obj C → Obj C
      G₀ x = F₀ F (e ,' x)
      
      G₁ : {a b : Obj C} → Hom C a b → Hom C (G₀ a) (G₀ b)
      G₁ f = F₁ F (idC C {e} ,' f)
      
      idG : {a : Obj C} → G₁ (idC C {a}) ≡ idC C {G₀ a}
      idG {a} = idF F
      composeG : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} 
               → G₁ ((C ∘ g) f) ≡ (C ∘ G₁ g) (G₁ f)
      composeG {f = f} {g} = trans (cong (λ X → F₁ F (X ,' g ∘C f)) (sym (left-id C))) (compose F)

  -- (_ ⊗ 1) ⇒ _
  rightUnitor : Obj C → Functor (C ×C C) C → Functor C C
  rightUnitor e F = functor G₀ G₁ idG composeG
    where
      G₀ : Obj C → Obj C
      G₀ x = F₀ F (x ,' e)
      
      G₁ : {a b : Obj C} → Hom C a b → Hom C (G₀ a) (G₀ b)
      G₁ f = F₁ F (f ,' idC C {e})
      
      idG : {a : Obj C} → G₁ (idC C {a}) ≡ idC C {G₀ a}
      idG {a} = idF F
      composeG : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} 
               → G₁ ((C ∘ g) f) ≡ (C ∘ G₁ g) (G₁ f)
      composeG {f = f} {g} = trans (cong (λ X → F₁ F (g ∘C f ,' X)) (sym (left-id C))) (compose F)

open FunctorApplication public

-------------------------------------------------------------------------------
-- Definition of Monoidal Categories
-------------------------------------------------------------------------------
record MonoidalCategory {ℓ₀ ℓ₁ : Level} (C : Category {ℓ₀} {ℓ₁}) : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  constructor monoidalCategory
  
  open Category C public
  
  field
    tensor : Functor (C ×C C) C -- ⊗ = \otimes
    
    unit : Obj
  
  open Functor hiding ( id )
  
  _⊗₀_ : (a b : Obj) → Obj
  _⊗₀_  a b = F₀ tensor (a ,' b)
  
  _⊗₁_ : {a b c d : Obj} → (f : Hom a b) → (g : Hom c d) → Hom (a ⊗₀ c) (b ⊗₀ d)
  _⊗₁_ f g = F₁ tensor (f ,' g)
  
  field 
    associator : NaturalIsomorphism (leftAssociator tensor) (rightAssociator tensor)
    
    left-unitor : NaturalIsomorphism (leftUnitor unit tensor) Id[ C ]
    
    right-unitor : NaturalIsomorphism (rightUnitor unit tensor) Id[ C ]
    
  open NaturalIsomorphism using ( η )
  
  α : (x y z : Obj) → Hom ((x ⊗₀ y) ⊗₀ z) (x ⊗₀ (y ⊗₀ z))
  α x y z = η associator (x , y , z)
  
  λ' : (x : Obj) → Hom (unit ⊗₀ x) x
  λ' x = η left-unitor x
  
  ρ : (x : Obj) → Hom (x ⊗₀ unit) x
  ρ x = η right-unitor x
  
  
  field
    triangle-id : (x y : Obj) → (ρ x ⊗₁ id {y}) ≡ (id {x} ⊗₁ λ' y) ∘ α x unit y
    
    pentagon-id : (w x y z : Obj) 
                → (id {w} ⊗₁ α x y z) ∘ (α w (x ⊗₀ y) z ∘ (α w x y ⊗₁ id {z})) ≡ α w x (y ⊗₀ z) ∘ α (w ⊗₀ x) y z
  
