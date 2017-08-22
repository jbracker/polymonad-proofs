
module Theory.TwoFunctor.Equality where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; proof-irrelevance to het-proof-irrelevance )
open ≡-Reasoning

-- Local
open import Utilities
open import Extensionality
open import Congruence
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Examples
open import Theory.Natural.Transformation
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.CodiscreteHomCat
open import Theory.TwoFunctor.Definition

-------------------------------------------------------------------------------
-- Definition of 2-Functors
-------------------------------------------------------------------------------

open Category hiding ( left-id ; right-id ; assoc ) renaming ( id to idC )
open StrictTwoCategory

-- horizontal composite:  ∘  =   _∘ₕ_  = flip (;)
-- vertical composite:    •  =   _∘ᵥ_
abstract
  lax-two-functor-eq : {ℓC₀ ℓC₁ ℓC₂ ℓD₀ ℓD₁ ℓD₂ : Level} 
                     → {C : StrictTwoCategory {ℓC₀} {ℓC₁} {ℓC₂}} 
                     → {D : StrictTwoCategory {ℓD₀} {ℓD₁} {ℓD₂}}
                     → {P₀₀ : Cell₀ C → Cell₀ D}
                     → {P₀₁ : Cell₀ C → Cell₀ D}
                     → {P₁₀ : {x y : Cell₀ C} → Functor (HomCat C x y) (HomCat D (P₀₀ x) (P₀₀ y))}
                     → {P₁₁ : {x y : Cell₀ C} → Functor (HomCat C x y) (HomCat D (P₀₁ x) (P₀₁ y))}
                     → {η₀ : {x : Cell₀ C} → Cell₂ D (id₁ D {P₀₀ x}) ([ P₁₀ {x} {x} ]₀ (id₁ C {x}))}
                     → {η₁ : {x : Cell₀ C} → Cell₂ D (id₁ D {P₀₁ x}) ([ P₁₁ {x} {x} ]₀ (id₁ C {x}))}
                     → {μ₀ : {x y z : Cell₀ C} {f : Cell₁ C x y} {g : Cell₁ C y z} → Cell₂ D (_∘ₕ_ D ([ P₁₀ ]₀ g) ([ P₁₀ ]₀ f)) ([ P₁₀ ]₀ (_∘ₕ_ C g f))}
                     → {μ₁ : {x y z : Cell₀ C} {f : Cell₁ C x y} {g : Cell₁ C y z} → Cell₂ D (_∘ₕ_ D ([ P₁₁ ]₀ g) ([ P₁₁ ]₀ f)) ([ P₁₁ ]₀ (_∘ₕ_ C g f))}
                     → {lfi₁₀ : {x y : Cell₀ C} {f : Cell₁ C x y} → _∘ᵥ_ D ([ P₁₀ {x} {y} ]₁ (λ' C f)) (_∘ᵥ_ D (μ₀ {x} {x} {y} {id₁ C {x}} {f}) (_∘ₕ₂_ D (id₂ D {f = [ P₁₀ {x} {y} ]₀ f}) (η₀ {x})) ) ≡ λ' D ([ P₁₀ {x} {y} ]₀ f)}
                     → {lfi₁₁ : {x y : Cell₀ C} {f : Cell₁ C x y} → _∘ᵥ_ D ([ P₁₁ {x} {y} ]₁ (λ' C f)) (_∘ᵥ_ D (μ₁ {x} {x} {y} {id₁ C {x}} {f}) (_∘ₕ₂_ D (id₂ D {f = [ P₁₁ {x} {y} ]₀ f}) (η₁ {x})) ) ≡ λ' D ([ P₁₁ {x} {y} ]₀ f)}
                     → {lfi₂₀ : {x y : Cell₀ C} {f : Cell₁ C x y} → _∘ᵥ_ D ([ P₁₀ {x} {y} ]₁ (ρ C f)) (_∘ᵥ_ D (μ₀ {x} {y} {y} {f} {id₁ C {y}}) (_∘ₕ₂_ D (η₀ {y}) (id₂ D {f = [ P₁₀ {x} {y} ]₀ f})) ) ≡ ρ D ([ P₁₀ {x} {y} ]₀ f)}
                     → {lfi₂₁ : {x y : Cell₀ C} {f : Cell₁ C x y} → _∘ᵥ_ D ([ P₁₁ {x} {y} ]₁ (ρ C f)) (_∘ᵥ_ D (μ₁ {x} {y} {y} {f} {id₁ C {y}}) (_∘ₕ₂_ D (η₁ {y}) (id₂ D {f = [ P₁₁ {x} {y} ]₀ f})) ) ≡ ρ D ([ P₁₁ {x} {y} ]₀ f)}
                     → {la₀ : {w x y z : Cell₀ C} {f : Cell₁ C w x} {g : Cell₁ C x y} {h : Cell₁ C y z} 
                            → _∘ᵥ_ D ([ P₁₀ {w} {z} ]₁ (α C f g h)) (_∘ᵥ_ D (μ₀ {w} {y} {z} {_∘ₕ_ C g f} {h}) (_∘ₕ₂_ D (id₂ D {P₀₀ y} {P₀₀ z} {[ P₁₀ {y} {z} ]₀ h}) (μ₀ {w} {x} {y} {f} {g})) ) 
                            ≡ _∘ᵥ_ D (μ₀ {w} {x} {z} {f} {_∘ₕ_ C h g}) 
                                     (_∘ᵥ_ D (_∘ₕ₂_ D (μ₀ {x} {y} {z} {g} {h}) (id₂ D {P₀₀ w} {P₀₀ x} {[ P₁₀ {w} {x} ]₀ f})) (α D ([ P₁₀ {w} {x} ]₀ f) ([ P₁₀ {x} {y} ]₀ g) ([ P₁₀ {y} {z} ]₀ h)) )}
                     → {la₁ : {w x y z : Cell₀ C} {f : Cell₁ C w x} {g : Cell₁ C x y} {h : Cell₁ C y z} 
                            → _∘ᵥ_ D ([ P₁₁ {w} {z} ]₁ (α C f g h)) (_∘ᵥ_ D (μ₁ {w} {y} {z} {_∘ₕ_ C g f} {h}) (_∘ₕ₂_ D (id₂ D {P₀₁ y} {P₀₁ z} {[ P₁₁ {y} {z} ]₀ h}) (μ₁ {w} {x} {y} {f} {g})) ) 
                            ≡ _∘ᵥ_ D (μ₁ {w} {x} {z} {f} {_∘ₕ_ C h g}) 
                                     (_∘ᵥ_ D (_∘ₕ₂_ D (μ₁ {x} {y} {z} {g} {h}) (id₂ D {P₀₁ w} {P₀₁ x} {[ P₁₁ {w} {x} ]₀ f})) (α D ([ P₁₁ {w} {x} ]₀ f) ([ P₁₁ {x} {y} ]₀ g) ([ P₁₁ {y} {z} ]₀ h)) )}
                     → (eqP₀ : P₀₀ ≡ P₀₁)
                     → (eqP₁ : (λ {x} {y} → P₁₀ {x} {y}) ≅ (λ {x} {y} → P₁₁ {x} {y}))
                     → (eq-η : (λ {x} → η₀ {x}) ≅ (λ {x} → η₁ {x}))
                     → (eq-μ : (λ {x} {y} {z} {f} {g} → μ₀ {x} {y} {z} {f} {g}) ≅ (λ {x} {y} {z} {f} {g} → μ₁ {x} {y} {z} {f} {g}))
                     → lax-two-functor {C = C} {D} P₀₀ P₁₀ η₀ μ₀ lfi₁₀ lfi₂₀ la₀ ≡ lax-two-functor {C = C} {D} P₀₁ P₁₁ η₁ μ₁ lfi₁₁ lfi₂₁ la₁
  lax-two-functor-eq {C = C} {D} {P₀} {.P₀} {P₁} {.P₁} {η} {.η} {μ} {.μ} {lfi₁₀} {lfi₁₁} {lfi₂₀} {lfi₂₁} {la₀} {la₁} refl hrefl hrefl hrefl 
    = cong₃ (lax-two-functor {C = C} {D} P₀ P₁ η μ) p1 p2 p3
    where
      abstract
        p1 : (λ {x} {y} {f} → lfi₁₀ {x} {y} {f}) ≡ lfi₁₁
        p1 = implicit-fun-ext $ λ x → implicit-fun-ext $ λ y → implicit-fun-ext 
           $ λ f → proof-irrelevance (lfi₁₀ {x} {y} {f}) (lfi₁₁ {x} {y} {f})
      
      abstract
        p2 : (λ {x} {y} {f} → lfi₂₀ {x} {y} {f}) ≡ lfi₂₁
        p2 = implicit-fun-ext $ λ x → implicit-fun-ext $ λ y → implicit-fun-ext 
           $ λ f → proof-irrelevance (lfi₂₀ {x} {y} {f}) (lfi₂₁ {x} {y} {f})
      
      abstract
        p3 : (λ {w} {x} {y} {z} {f} {g} {h} → la₀ {w} {x} {y} {z} {f} {g} {h}) ≡ la₁
        p3 = implicit-fun-ext $ λ w → implicit-fun-ext $ λ x → implicit-fun-ext $ λ y → implicit-fun-ext $ λ z → implicit-fun-ext 
           $ λ f → implicit-fun-ext $ λ g → implicit-fun-ext $ λ h → proof-irrelevance (la₀ {w} {x} {y} {z} {f} {g} {h}) (la₁ {w} {x} {y} {z} {f} {g} {h})
