
open import Level
open import Function hiding ( id )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Category.Examples using ( [_,_] ; setCategory )
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Association
open Theory.Functor.Association.Associator
open import Theory.Functor.Application
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Properties
open import Theory.Natural.Isomorphism

open import Theory.End.DayConvolution

open import Extensionality

module Theory.Natural.Isomorphism.Examples.DayConvolutionAssociator where

open Category 

dayAssociator : {ℓC₀ ℓC₁ : Level} → (ℓSet : Level) → {C : Category {ℓC₀} {ℓC₁}} → (CMon : MonoidalCategory C)
              → NaturalIsomorphism (leftAssociator (dayConvolution {ℓSet = ℓSet} CMon)) (rightAssociator (dayConvolution {ℓSet = ℓSet} CMon))
dayAssociator {ℓC₀} {ℓC₁} ℓSet {C} CMon = naturalIsomorphism {!η!} {!!}
  where
    dayConv = dayConvolution {ℓSet = ℓSet} CMon
    lAssoc = leftAssociator dayConv
    rAssoc = rightAssociator dayConv
