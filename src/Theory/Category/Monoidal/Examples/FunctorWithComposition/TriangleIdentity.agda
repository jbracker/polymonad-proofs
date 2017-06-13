
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Category.Examples renaming ( functorCategory to Fun )
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Association
open import Theory.Functor.Application
open import Theory.Functor.Examples.CompositionFunctor renaming ( compositionFunctor to CompF )
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Properties
open import Theory.Natural.Isomorphism
open import Theory.Natural.Isomorphism.Examples.FunctorCompositionAssociator renaming ( functorCompositionAssociatorIso to fcaIso )
open import Theory.Natural.Isomorphism.Examples.FunctorCompositionLeftUnitor renaming ( functorCompositionLeftUnitorIso to fclIso )
open import Theory.Natural.Isomorphism.Examples.FunctorCompositionRightUnitor renaming ( functorCompositionRightUnitorIso to fcrIso )

open import Extensionality

module Theory.Category.Monoidal.Examples.FunctorWithComposition.TriangleIdentity where

open Category
open NaturalTransformation
open NaturalIsomorphism renaming ( η to iso-η )

open Theory.Functor.Association.Associator
open Theory.Functor.Application.BiFunctor

triangle-id 
  : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) 
  → (x y : Obj (Fun C C)) 
  → Functor.F₁ (CompF C C C) (iso-η (fcrIso C) x , id (Fun C C))
  ≡ (Fun C C ∘ Functor.F₁ (CompF C C C) (id (Fun C C) , iso-η (fclIso C) y)) (iso-η (fcaIso C) (x ,' Id[ C ] ,' y))
triangle-id C = {!!}
