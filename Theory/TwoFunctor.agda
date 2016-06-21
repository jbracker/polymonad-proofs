 
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
open TwoCategory renaming ( id to id2C ; comp to comp2C )

record TwoFunctor {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓD₂ : Level} (C : Category {ℓC₀} {ℓC₁}) (D : TwoCategory {ℓD₀} {ℓD₁} {ℓD₂}) : Set (lsuc (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ ℓD₂)) where
  field
    F₀ : Obj C → Cell₀ D
    F₁ : {a b : Obj C} → Hom C a b → Functor (Cell₁ D (F₀ a) (F₀ a)) (Cell₁ D (F₀ b) (F₀ b))
    
    id : {a : Obj C}
       -- (a a ↦ a a) ∼ (F₁ (a → a))
       → NaturalTransformation _≡_ Id[ Cell₁ D (F₀ a) (F₀ a) ] (F₁ (idC C {a}))

    comp : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c}
         -- (F₁ g ∘ F₁ f) ∼ F₁ (g ∘ f)
         → NaturalTransformation _≡_ [ F₁ g ]∘[ F₁ f ] (F₁ (_∘_ C g f))
