
module Theory.Subcategory where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Theory.Category


open Category renaming ( _∘_ to comp )

record Subcategory {ℓ₀ ℓ₁ : Level} (C : Category {ℓ₀} {ℓ₁}) : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  constructor subcategory
  _∘_ = comp C
  
  field
    SubObj : SubsetOf (Obj C)
    SubHom : (a : Obj C) → (b : Obj C) → SubsetOf (Hom C a b)
    
    closedMorphs : {a b : Obj C} → (f : Hom C a b) 
                 → f ∈ SubHom a b → (a ∈ SubObj) × (b ∈ SubObj)
    
    closedTrans : {a b c : Obj C} → (f : Hom C a b) → (g : Hom C b c)
                → (f ∈ SubHom a b) → (g ∈ SubHom b c) → ((g ∘ f) ∈ SubHom a c)
    
    closedId : {a : Obj C} → (a ∈ SubObj) → (id C ∈ SubHom a a)

    
