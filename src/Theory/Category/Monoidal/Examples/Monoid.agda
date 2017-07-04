
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

module Theory.Category.Monoidal.Examples.Monoid where

monoidMonoidalCategory : {ℓ : Level} {A : Set ℓ} → (mon : Monoid A) → MonoidalCategory (codiscreteCategory A)
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
    
    tensor : Functor (codiscreteCategory A ×C codiscreteCategory A) (codiscreteCategory A)
    tensor = functor (λ x → proj₁ x ∙ proj₂ x) (λ _ → lift tt) refl refl
    
    associator : NaturalIsomorphism (leftAssociator tensor) (rightAssociator tensor)
    associator = naturalIsomorphism (naturalTransformation (λ x → lift tt) refl) (λ x → isomorphism (lift tt) refl refl)
    
    left-unitor : NaturalIsomorphism ([ Monoid.ε mon ,-] tensor) Id[ codiscreteCategory A ]
    left-unitor = naturalIsomorphism (naturalTransformation (λ x → lift tt) refl) (λ x → isomorphism (lift tt) refl refl)
    
    right-unitor : NaturalIsomorphism ([-, Monoid.ε mon ] tensor) Id[ codiscreteCategory A ]
    right-unitor = naturalIsomorphism (naturalTransformation (λ x → lift tt) refl) (λ x → isomorphism (lift tt) refl refl)
