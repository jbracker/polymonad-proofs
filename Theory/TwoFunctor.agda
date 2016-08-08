 
module Theory.TwoFunctor where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation
open import Theory.Examples.Functor
open import Theory.TwoCategory

-------------------------------------------------------------------------------
-- Definition of 2-Functors
-------------------------------------------------------------------------------
open Category hiding ( idL ; idR ; assoc ) renaming ( id to idC )
open StrictTwoCategory

record LaxTwoFunctor {ℓC₀ ℓC₁ ℓC₂ ℓD₀ ℓD₁ ℓD₂ : Level} 
                     (C : StrictTwoCategory {ℓC₀} {ℓC₁} {ℓC₂}) 
                     (D : StrictTwoCategory {ℓD₀} {ℓD₁} {ℓD₂}) 
                     : Set (lsuc (ℓC₀ ⊔ ℓC₁ ⊔ ℓC₂ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ ℓD₂)) where
  private
    _▷D_ = _▷_ D
    _▷C_ = _▷_ C

    _◁D_ = _◁_ D
    _◁C_ = _◁_ C
    
    _∘Dₕ_ = _∘ₕ_ D
    _∘Cₕ_ = _∘ₕ_ C

    _∘Dₕ₂_ = _∘ₕ₂_ D

    _∘Dᵥ_ = _∘ᵥ_ D
    _∘Cᵥ_ = _∘ᵥ_ C

    id₁D = id₁ D

  field
    -- Names and structure base on: https://ncatlab.org/nlab/show/pseudofunctor
    
    -- P_{x}
    P₀ : Cell₀ C → Cell₀ D
    -- P_{x,y}
    P₁ : {x y : Cell₀ C} → Functor (HomCat C x y) (HomCat D (P₀ x) (P₀ y))
    
    -- P_{id_x}
    η : {x : Cell₀ C}
      → Cell₂ D (id₁ D {P₀ x}) ([ P₁ {x} {x} ]₀ (id₁ C {x}))

    -- P_{x,y,z}
    μ : {x y z : Cell₀ C} {f : Cell₁ C x y} {g : Cell₁ C y z}
         -- (F₁ g ∘ F₁ f) ∼ F₁ (g ∘ f)
         → Cell₂ D ([ P₁ ]₀ g  ∘Dₕ  [ P₁ ]₀ f) ([ P₁ ]₀ (g ∘Cₕ f))
    
    lawId₁ : {x y : Cell₀ C} {f : Cell₁ C x y} 
           → ([ P₁ {x} {y} ]₁ (λ' C f)) 
         ∘Dᵥ ( (μ {x} {x} {y} {id₁ C {x}} {f}) 
         ∘Dᵥ   (id₂ D {f = [ P₁ {x} {y} ]₀ f} ∘Dₕ₂ η {x}) )
           ≡ λ' D ([ P₁ {x} {y} ]₀ f)
    
    lawId₂ : {x y : Cell₀ C} {f : Cell₁ C x y} 
           → ([ P₁ {x} {y} ]₁ (ρ C f)) 
         ∘Dᵥ ( (μ {x} {y} {y} {f} {id₁ C {y}}) 
         ∘Dᵥ   (η {y} ∘Dₕ₂ id₂ D {f = [ P₁ {x} {y} ]₀ f}) ) 
           ≡ ρ D ([ P₁ {x} {y} ]₀ f)
    
-- horizontal composite:  ∘  =   _∘ₕ_
-- vertical composite:    •  =   _∘ᵥ_
