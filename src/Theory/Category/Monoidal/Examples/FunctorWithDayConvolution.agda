
open import Level
open import Function hiding ( id )

open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ( [_] )
open ≡-Reasoning

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Category.Examples.SetCat using ( setCategory )
open import Theory.Category.Examples.Functor using ( [_,_]  )
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Association
open Theory.Functor.Association.Associator
open import Theory.Functor.Application
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Properties
open import Theory.Natural.Isomorphism

open import Theory.End.DayConvolution
open import Theory.End.DayUnit

open import Extensionality

open import Theory.Category.Monoidal.Examples.FunctorWithDayConvolution.Postulates
open import Theory.Category.Monoidal.Examples.FunctorWithDayConvolution.Postulates.TriangleId
open import Theory.Category.Monoidal.Examples.FunctorWithDayConvolution.Postulates.PentagonId

module Theory.Category.Monoidal.Examples.FunctorWithDayConvolution where

open Category

functorDayMonoidalCategory : {ℓC₀ ℓC₁ : Level} → (ℓSet : Level) → {C : Category {ℓC₀} {ℓC₁}}
                        → MonoidalCategory C
                        → MonoidalCategory [ C , (setCategory {ℓSet ⊔ ℓC₀ ⊔ ℓC₁}) ]
functorDayMonoidalCategory {ℓC₀} {ℓC₁} ℓSet {C} CMon = record
  { tensor = dayConvolution {ℓSet = ℓSet} CMon
  ; unit = dayUnit {ℓSet = ℓSet} CMon
  ; associator = dayAssociator ℓSet CMon
  ; left-unitor = dayLeftUnitor ℓSet CMon
  ; right-unitor = dayRightUnitor ℓSet CMon
  ; triangle-id = day-triangle-id ℓSet CMon
  ; pentagon-id = day-pentagon-id ℓSet CMon
  }
