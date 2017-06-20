
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
open import Theory.Functor.Application
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Properties
open import Theory.Natural.Isomorphism

open import Theory.End.DayConvolution
open import Theory.End.DayUnit

open import Extensionality

module Theory.Category.Monoidal.Examples.FunctorWithDayConvolution where

open Category

functorMonoidalCategory : {ℓC₀ ℓC₁ : Level} → (ℓSet : Level) → {C : Category {ℓC₀} {ℓC₁}}
                        → MonoidalCategory C
                        → MonoidalCategory [ C , (setCategory {ℓSet ⊔ ℓC₀ ⊔ ℓC₁}) ]
functorMonoidalCategory {ℓC₀} {ℓC₁} ℓSet {C} CMon = record
  { tensor = dayConvolution {ℓSet = ℓSet} CMon
  ; unit = dayUnit {ℓSet = ℓSet} CMon
  ; associator = {!!}
  ; left-unitor = {!!}
  ; right-unitor = {!!}
  ; triangle-id = {!!}
  ; pentagon-id = {!!}
  }
