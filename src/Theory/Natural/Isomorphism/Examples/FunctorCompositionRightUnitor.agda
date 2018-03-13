
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Category.Definition
open import Theory.Category.Isomorphism
open import Theory.Category.Examples.Functor using ( functorCategory )
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Application
open import Theory.Functor.Examples.CompositionFunctor
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples.FunctorCompositionRightUnitor
open import Theory.Natural.Isomorphism

module Theory.Natural.Isomorphism.Examples.FunctorCompositionRightUnitor where

open Category
open NaturalTransformation renaming ( η to nat-η )
open Theory.Functor.Application.BiFunctor

functorCompositionRightUnitorIso : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) → NaturalIsomorphism ([-, Id[ C ] ] (compositionFunctor C C C)) Id[ functorCategory C C ]
functorCompositionRightUnitorIso C = naturalIsomorphism (functorCompositionRightUnitor C) iso
  where
    Fun = functorCategory C C
    comp = compositionFunctor C C C

    iso : (F : Functor C C) → Isomorphism Fun (nat-η (functorCompositionRightUnitor C) F)
    iso (functor F₀ F₁ F-id F-compose) = isomorphism (nat-η (functorCompositionRightUnitor' C) F) left-id' right-id'
      where 
        F = functor F₀ F₁ F-id F-compose
        
        abstract
          left-id' : ⟨ nat-η (functorCompositionRightUnitor C) F ⟩∘ᵥ⟨ nat-η (functorCompositionRightUnitor' C) F ⟩ ≡ id Fun
          left-id' = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → right-id C
        
        abstract
          right-id' : ⟨ nat-η (functorCompositionRightUnitor' C) F ⟩∘ᵥ⟨ nat-η (functorCompositionRightUnitor C) F ⟩ ≡ id Fun
          right-id' = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → right-id C
