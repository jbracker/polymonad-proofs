 
module Theory.Category.Monoidal where

open import Level renaming ( zero to lzero ; suc to lsuc )
open import Data.Product renaming ( _,_ to _,'_ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.HeterogeneousEquality using ( _≅_ )

open import Theory.Triple
open import Theory.Category hiding ( category )
open import Theory.Category.Isomorphism
open import Theory.Functor
import Theory.Functor.Association
import Theory.Functor.Application
open import Theory.Natural.Transformation
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
  
  open Theory.Functor.Association.Associator
  open Theory.Functor.Application.BiFunctor
  
  field 
    associator : NaturalIsomorphism (leftAssociator tensor) (rightAssociator tensor)
    
    left-unitor : NaturalIsomorphism ([ unit ,-] tensor) Id[ C ]
    
    right-unitor : NaturalIsomorphism ([-, unit ] tensor) Id[ C ]
    
  open NaturalIsomorphism using ( η ; isomorphic ) renaming ( natural-transformation to nat-trans )
  
  α : (x y z : Obj) → Hom ((x ⊗₀ y) ⊗₀ z) (x ⊗₀ (y ⊗₀ z))
  α x y z = η associator (x , y , z)
  
  λ' : (x : Obj) → Hom (unit ⊗₀ x) x
  λ' x = η left-unitor x
  
  ρ : (x : Obj) → Hom (x ⊗₀ unit) x
  ρ x = η right-unitor x
  
  open NaturalTransformation (nat-trans associator)   renaming (natural to α-natural) hiding (η) public
  open NaturalTransformation (nat-trans left-unitor)  renaming (natural to λ-natural) hiding (η) public
  open NaturalTransformation (nat-trans right-unitor) renaming (natural to ρ-natural) hiding (η) public
  
  field
    triangle-id : (x y : Obj) → (ρ x ⊗₁ id {y}) ≡ (id {x} ⊗₁ λ' y) ∘ α x unit y
    
    pentagon-id : (w x y z : Obj) 
                → (id {w} ⊗₁ α x y z) ∘ (α w (x ⊗₀ y) z ∘ (α w x y ⊗₁ id {z})) ≡ α w x (y ⊗₀ z) ∘ α (w ⊗₀ x) y z
    
  category : Category
  category = Category.category Obj Hom _∘_ id assoc right-id left-id
  

private
  module MonoidalCategoryAccessors {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}} (MC : MonoidalCategory C) where
    
    open MonoidalCategory MC
    open Isomorphism
    open NaturalIsomorphism using ( isomorphic )
    
    private
      module AssociatorInv (x y z : Obj) where
        open Isomorphism (isomorphic associator (x , y , z)) hiding ( f⁻¹ ) renaming ( inv to α-inv ; left-id to α-left-id ; right-id to α-right-id ) public
    open AssociatorInv public
    
    private
      module UnitorInvs (x : Obj) where
        open Isomorphism (isomorphic left-unitor  x) hiding ( f⁻¹ ) renaming ( inv to λ-inv ; left-id to λ-left-id ; right-id to λ-right-id ) public
        open Isomorphism (isomorphic right-unitor x) hiding ( f⁻¹ ) renaming ( inv to ρ-inv ; left-id to ρ-left-id ; right-id to ρ-right-id ) public
    open UnitorInvs public
    
open MonoidalCategoryAccessors public
