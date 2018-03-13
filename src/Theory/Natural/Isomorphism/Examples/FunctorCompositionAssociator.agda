
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Isomorphism
open import Theory.Category.Examples.Functor
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Association
open import Theory.Functor.Examples.CompositionFunctor
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples.FunctorCompositionAssociator 
open import Theory.Natural.Isomorphism

module Theory.Natural.Isomorphism.Examples.FunctorCompositionAssociator where

open Category
open NaturalTransformation renaming ( η to nat-η )
open Theory.Functor.Association.Associator

functorCompositionAssociatorIso : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) → NaturalIsomorphism (leftAssociator (compositionFunctor C C C)) (rightAssociator (compositionFunctor C C C))
functorCompositionAssociatorIso C = naturalIsomorphism (functorCompositionAssociator C) iso -- (fca C) {!!}
  where
    Fun = functorCategory C C
    comp = compositionFunctor C C C
    _∘C_ = _∘_ C
    lAssoc = leftAssociator comp
    rAssoc = rightAssociator comp

    iso : (x : Obj (Fun ×C Fun ×C Fun)) → Isomorphism Fun (nat-η (functorCompositionAssociator C) x)
    iso x = isomorphism (nat-η (functorCompositionAssociator' C) x) iso-id₁ iso-id₂
      where
        abstract
          iso-id₁ : ⟨ nat-η (functorCompositionAssociator C) x ⟩∘ᵥ⟨ nat-η (functorCompositionAssociator' C) x ⟩ ≡ id Fun
          iso-id₁ = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → left-id C
        
        abstract
          iso-id₂ : ⟨ nat-η (functorCompositionAssociator' C) x ⟩∘ᵥ⟨ nat-η (functorCompositionAssociator C) x ⟩ ≡ id Fun
          iso-id₂ = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → left-id C
