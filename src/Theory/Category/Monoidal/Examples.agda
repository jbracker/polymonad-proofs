
open import Level
open import Function hiding ( id )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Theory.Monoid
open import Theory.Category
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Category.Examples renaming ( setCategory to SetCat )
open import Theory.Functor
open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

module Theory.Category.Monoidal.Examples where

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

NoHomCat : {ℓ : Level} → (A : Set ℓ) → Category
NoHomCat A = category A (λ _ _ → ⊤) (λ _ _ → tt) tt refl refl refl

monoidMonoidalCategory : {ℓ : Level} {A : Set ℓ} → (mon : Monoid A) → MonoidalCategory (NoHomCat A)
monoidMonoidalCategory {ℓ} {A} mon = record
  { tensor = tensor
  ; unit = Monoid.ε mon
  ; associator = associator
  ; left-unitor = left-unitor
  ; right-unitor = right-unitor
  ; triangle-id = λ x y → refl
  ; pentagon-id = λ w x y z → refl
  } where
    open import Theory.Triple
    open import Theory.Functor.Association
    open import Theory.Functor.Application
    open Theory.Triple.Triple renaming ( proj₁ to proj₁' ; proj₂ to proj₂' )
    open Theory.Functor.Association.Associator
    open Theory.Functor.Application.BiFunctor
    
    _∙_ = Monoid._∙_ mon
    
    tensor : Functor (NoHomCat A ×C NoHomCat A) (NoHomCat A)
    tensor = functor (λ x → proj₁ x ∙ proj₂ x) (λ _ → tt) refl refl
    
    associator : NaturalIsomorphism (leftAssociator tensor) (rightAssociator tensor)
    associator = naturalIsomorphism (naturalTransformation (λ x → tt) refl) (λ x → isomorphism tt refl refl)
    
    left-unitor : NaturalIsomorphism ([ Monoid.ε mon ,-] tensor) Id[ NoHomCat A ]
    left-unitor = naturalIsomorphism (naturalTransformation (λ x → tt) refl) (λ x → isomorphism tt refl refl)
    
    right-unitor : NaturalIsomorphism ([-, Monoid.ε mon ] tensor) Id[ NoHomCat A ]
    right-unitor = naturalIsomorphism (naturalTransformation (λ x → tt) refl) (λ x → isomorphism tt refl refl)
