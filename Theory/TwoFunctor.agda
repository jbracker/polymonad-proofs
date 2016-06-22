 
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
open StrictTwoCategory renaming ( id to id2C ; comp to comp2C )

record LaxTwoFunctor {ℓC₀ ℓC₁ ℓC₂ ℓD₀ ℓD₁ ℓD₂ : Level} 
                     (C : StrictTwoCategory {ℓC₀} {ℓC₁} {ℓC₂}) 
                     (D : StrictTwoCategory {ℓD₀} {ℓD₁} {ℓD₂}) 
                     : Set (lsuc (ℓC₀ ⊔ ℓC₁ ⊔ ℓC₂ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ ℓD₂)) where
  field
    F₀ : Cell₀ C → Cell₀ D
    F₁ : {a b : Cell₀ C} → Functor (HomCat C a b) (HomCat D (F₀ a) (F₀ b))
    
    id : {a : Cell₀ C}
       → {fd : Cell₁ D (F₀ a) (F₀ a)} {fc : Cell₁ C a a}
       -- (a a ↦ a a) ∼ (F₁ (a → a))
       → Cell₂ D fd ([ F₁ ]₀ fc)

    comp : {a b c : Cell₀ C} {f : Cell₁ C a b} {g : Cell₁ C b c }
         -- (F₁ g ∘ F₁ f) ∼ F₁ (g ∘ f)
         → Cell₂ D (_∘ₕ_ D ([ F₁ ]₀ g) ([ F₁ ]₀ f)) ([ F₁ ]₀ (_∘ₕ_ C g f))
