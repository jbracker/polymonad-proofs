
open import Level
open import Function hiding ( id )

open import Data.Product

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
open import Theory.Natural.Transformation.Examples.FunctorCompositionLeftUnitor
open import Theory.Natural.Isomorphism

module Theory.Natural.Isomorphism.Examples.FunctorCompositionLeftUnitor where

open Category
open NaturalTransformation renaming ( η to nat-η )
open Theory.Functor.Application.BiFunctor

functorCompositionLeftUnitorIso : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) → NaturalIsomorphism ([ Id[ C ] ,-] (compositionFunctor C C C)) Id[ functorCategory C C ]
functorCompositionLeftUnitorIso C = naturalIsomorphism (functorCompositionLeftUnitor C) iso
  where
    Fun = functorCategory C C
    comp = compositionFunctor C C C
    _∘C_ = Category._∘_ C
    
    iso : (F : Functor C C) → Isomorphism Fun (nat-η (functorCompositionLeftUnitor C) F)
    iso F = isomorphism (nat-η (functorCompositionLeftUnitor' C) F) left-id' right-id'
      where
        abstract
          left-id' : ⟨ nat-η (functorCompositionLeftUnitor C) F ⟩∘ᵥ⟨ nat-η (functorCompositionLeftUnitor' C) F ⟩ ≡ id Fun
          left-id' = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → left-id C
        
        abstract
          right-id' : ⟨ nat-η (functorCompositionLeftUnitor' C) F ⟩∘ᵥ⟨ nat-η (functorCompositionLeftUnitor C) F ⟩ ≡ id Fun
          right-id' = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → left-id C
