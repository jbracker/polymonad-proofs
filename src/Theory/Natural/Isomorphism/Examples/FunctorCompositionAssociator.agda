
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Isomorphism
open import Theory.Category.Examples
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Association
open import Theory.Functor.Examples.CompositionFunctor
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples.FunctorCompositionAssociator renaming ( functorCompositionAssociator to fca ; functorCompositionAssociator' to fca' )
open import Theory.Natural.Isomorphism

module Theory.Natural.Isomorphism.Examples.FunctorCompositionAssociator 
  {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) where

open Category
open NaturalTransformation renaming ( η to nat-η )
open Theory.Functor.Association.Associator

private
  Fun = functorCategory C C
  comp = compositionFunctor C C C
  _∘C_ = _∘_ C
  lAssoc = leftAssociator comp
  rAssoc = rightAssociator comp

-- fca : NaturalTransformation lAssoc rAssoc
 
functorCompositionAssociator : NaturalIsomorphism lAssoc rAssoc
functorCompositionAssociator = naturalIsomorphism nat iso -- (fca C) {!!}
  where
    nat : NaturalTransformation lAssoc rAssoc
    nat = {!fca {ℓC₀} {ℓC₁} C!}
    
    iso : (x : Obj (Fun ×C Fun ×C Fun)) → Isomorphism Fun (nat-η nat x)
    iso x = isomorphism (nat-η (fca' C) x) {!!} {!!}
