
open import Level
open import Function hiding ( id )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Category.Examples.Functor using ( functorCategory )
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Association
open import Theory.Functor.Application
open import Theory.Functor.Examples.CompositionFunctor
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Properties
open import Theory.Natural.Isomorphism
open import Theory.Natural.Isomorphism.Examples.FunctorCompositionAssociator
open import Theory.Natural.Isomorphism.Examples.FunctorCompositionLeftUnitor
open import Theory.Natural.Isomorphism.Examples.FunctorCompositionRightUnitor
open import Theory.Category.Monoidal.Examples.FunctorWithComposition.TriangleIdentity
open import Theory.Category.Monoidal.Examples.FunctorWithComposition.PentagonIdentity

open import Extensionality

module Theory.Category.Monoidal.Examples.FunctorWithComposition where

open Category
open NaturalTransformation
open NaturalIsomorphism renaming ( natural-transformation to nat-trans ; η to iso-η )

open Theory.Functor.Association.Associator
open Theory.Functor.Application.BiFunctor

functorMonoidalCategory : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) → MonoidalCategory (functorCategory C C)
functorMonoidalCategory C = record
  { tensor = compositionFunctor C C C
  ; unit = Id[ C ]
  ; associator = functorCompositionAssociatorIso C
  ; left-unitor = functorCompositionLeftUnitorIso C
  ; right-unitor = functorCompositionRightUnitorIso C
  ; triangle-id = triangle-id C
  ; pentagon-id = pentagon-id C
  }
