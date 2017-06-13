
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

open import Extensionality

module Theory.Category.Monoidal.Examples.FunctorWithComposition.PentagonIdentity where

open Category
open Functor renaming ( id to functor-id )
open NaturalTransformation renaming ( η to nat-η )
open NaturalIsomorphism renaming ( η to iso-η )

pentagon-id 
  : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) 
  → (w x y z : Obj (Fun C C)) 
  → (Fun C C ∘ F₁ (CompF C C C) (id (Fun C C) , iso-η (fcaIso C) (x ,' y ,' z))) ((Fun C C ∘ iso-η (fcaIso C) (w ,' F₀ (CompF C C C) (x , y) ,' z)) (F₁ (CompF C C C) (iso-η (fcaIso C) (w ,' x ,' y) , id (Fun C C))))
  ≡ (Fun C C ∘ iso-η (fcaIso C) (w ,' x ,' F₀ (CompF C C C) (y , z))) (iso-η (fcaIso C) (F₀ (CompF C C C) (w , x) ,' y ,' z))
pentagon-id C F G H I = {!!}
