 
module Theory.NaturalIsomorphism where

open import Level renaming ( zero to lzero ; suc to lsuc )
open import Relation.Binary.PropositionalEquality


open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation

-- Definition of a natural isomorphism: 
-- https://ncatlab.org/nlab/show/natural+isomorphism
-- A natural isomorphism is a natural transformation where every
-- arrow mapped by the natural transformation has an inverse arrow
-- that is its left and right identity.
record NaturalIsomorphism {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                          {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                          (F : Functor C D) (G : Functor C D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  constructor naturalIsomorphism
  field
    natTrans : NaturalTransformation F G

  open NaturalTransformation natTrans public
  
  open Category hiding ( idL ; idR )
  open Functor hiding ( id )
  private
    _∘D_ = _∘_ D
  
  field
    inv : {x : Obj C} → Hom D ([ F ]₀ x) ([ G ]₀ x) → Hom D ([ G ]₀ x) ([ F ]₀ x)
    
    invIdL : {x : Obj C} → η x ∘D inv (η x) ≡ id D {[ G ]₀ x}

    invIdR : {x : Obj C} → inv (η x) ∘D η x ≡ id D {[ F ]₀ x}
  
  
  
  
