 
module Theory.NaturalIsomorphism where

open import Level renaming ( zero to lzero ; suc to lsuc )
open import Relation.Binary.PropositionalEquality

open import Utilities
open import Theory.Isomorphism
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation

  
open Category hiding ( idL ; idR )

-------------------------------------------------------------------------------
-- Definition of a natural isomorphism: 
-- https://ncatlab.org/nlab/show/natural+isomorphism
-- A natural isomorphism is a natural transformation where every
-- arrow mapped by the natural transformation has an inverse arrow
-- that is its left and right identity.
-------------------------------------------------------------------------------
record NaturalIsomorphism {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                          {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                          (F : Functor C D) (G : Functor C D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  constructor naturalIsomorphism
  field
    natTrans : NaturalTransformation F G

  open NaturalTransformation natTrans public
  open Functor hiding ( id )
  private
    _∘D_ = _∘_ D
  
  field
    isomorphic : {x : Obj C} → (f : Hom D ([ F ]₀ x) ([ G ]₀ x)) → Isomorphism D f
  
  private
    module Isomorphic {x : Obj C} (f : Hom D ([ F ]₀ x) ([ G ]₀ x)) where
      iso = isomorphic {x} f
      open Isomorphism iso hiding ( f⁻¹ ) public
  
  open Isomorphic public

-------------------------------------------------------------------------------
-- Equality of natural isomorphisms
-------------------------------------------------------------------------------
natural-isomorphism-eq : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                       → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                       → {F : Functor C D} {G : Functor C D}
                       → {nat nat' : NaturalTransformation F G}
                       → {iso iso' : {x : Obj C} → (f : Hom D ([ F ]₀ x) ([ G ]₀ x)) → Isomorphism D f}
                       → nat ≡ nat' → ({x : Obj C} → (f : Hom D ([ F ]₀ x) ([ G ]₀ x)) → iso f ≡ iso' f)
                       → naturalIsomorphism nat iso ≡ naturalIsomorphism nat' iso'
natural-isomorphism-eq refl iso-eq = cong₂ naturalIsomorphism refl (funExtImplicit (λ x → funExt (λ f → iso-eq {x} f)))
