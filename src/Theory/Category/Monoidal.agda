 
module Theory.Category.Monoidal where

open import Level renaming ( zero to lzero ; suc to lsuc )
open import Data.Product renaming ( _,_ to _,'_ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.HeterogeneousEquality using ( _≅_ )

open import Theory.Triple
open import Theory.Category
open import Theory.Functor
open import Theory.Functor.Examples
open import Theory.Natural.Isomorphism

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
  
  open Theory.Functor.Examples.Associator
  open Theory.Functor.Examples.BiFunctorApplication
  
  field 
    associator : NaturalIsomorphism (leftAssociator tensor) (rightAssociator tensor)
    
    left-unitor : NaturalIsomorphism ([ unit ,-] tensor) Id[ C ]
    
    right-unitor : NaturalIsomorphism ([-, unit ] tensor) Id[ C ]
    
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
  
