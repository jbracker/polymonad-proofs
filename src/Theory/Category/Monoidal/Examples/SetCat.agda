
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Category.Examples renaming ( setCategory to SetCat )
open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

module Theory.Category.Monoidal.Examples.SetCat where

setMonoidalCategory : {ℓ : Level} → MonoidalCategory (SetCat {ℓ})
setMonoidalCategory {ℓ} = record
  { tensor = record
    { F₀ = λ X → proj₁ X × proj₂ X
    ; F₁ = λ f a → proj₁ f (proj₁ a) , proj₂ f (proj₂ a)
    ; id = refl
    ; compose = refl
    }
  ; unit = Lift ⊤
  ; associator = record
    { natural-transformation = record
      { η = λ X x → proj₁ (proj₁ x) , (proj₂ (proj₁ x)) , (proj₂ x)
      ; natural = refl
      }
    ; isomorphic = λ X → record
      { f⁻¹ = λ x → (proj₁ x , proj₁ (proj₂ x)) , proj₂ (proj₂ x)
      ; left-id = refl
      ; right-id = refl
      }
    }
  ; left-unitor = record
    { natural-transformation = record
      { η = λ X x → proj₂ x
      ; natural = refl
      }
    ; isomorphic = λ X → record
      { f⁻¹ = λ x → lift tt , x
      ; left-id = refl
      ; right-id = refl
      }
    }
  ; right-unitor = record
    { natural-transformation = record
      { η = λ X x → proj₁ x
      ; natural = refl
      }
    ; isomorphic = λ X → record
      { f⁻¹ = λ x → x , lift tt
      ; left-id = refl
      ; right-id = refl
      }
    }
  ; triangle-id = λ x y → refl
  ; pentagon-id = λ w x y z → refl
  } 
