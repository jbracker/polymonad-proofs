
-- StdLib
open import Level renaming ( zero to lzero ; suc to lsuc )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

-- Local
open import Extensionality
open import Theory.Category
open import Theory.Category.Isomorphism
open import Theory.Functor
open import Theory.Natural.Transformation

module Theory.Natural.Isomorphism where
  
open Category

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
    natural-transformation : NaturalTransformation F G

  open NaturalTransformation natural-transformation public
  open Functor hiding ( id )
  private
    _∘D_ = _∘_ D
  
  field
    isomorphic : (x : Obj C) → Isomorphism D (η x)
  
  private
    module Isomorphic (x : Obj C) where
      iso = isomorphic x
      open Isomorphism iso hiding ( f⁻¹ ) public
  
  open Isomorphic public

-------------------------------------------------------------------------------
-- Equality of natural isomorphisms
-------------------------------------------------------------------------------
natural-isomorphism-eq : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                       → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                       → {F : Functor C D} {G : Functor C D}
                       → {nat₀ nat₁ : NaturalTransformation F G}
                       → {iso₀ : (x : Obj C) → Isomorphism D (NaturalTransformation.η nat₀ x)}
                       → {iso₁ : (x : Obj C) → Isomorphism D (NaturalTransformation.η nat₁ x)}
                       → nat₀ ≡ nat₁ → iso₀ ≅ iso₁
                       → naturalIsomorphism nat₀ iso₀ ≡ naturalIsomorphism nat₁ iso₁
natural-isomorphism-eq {nat₀ = nat} {.nat} {iso} {.iso} refl refl = refl
