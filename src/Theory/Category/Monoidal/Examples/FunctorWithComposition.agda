
open import Level
open import Function hiding ( id )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Category.Examples using ( functorCategory )
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

open import Extensionality

module Theory.Category.Monoidal.Examples.FunctorWithComposition where

open Category
open NaturalTransformation
open NaturalIsomorphism renaming ( natural-transformation to nat-trans ; η to iso-η )

open Theory.Functor.Association.Associator
open Theory.Functor.Application.BiFunctor

functorMonoidalCategory : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) → MonoidalCategory (functorCategory C C)
functorMonoidalCategory C = record
  { tensor = tensor
  ; unit = unit
  ; associator = functorCompositionAssociatorIso C
  ; left-unitor = functorCompositionLeftUnitorIso C
  ; right-unitor = functorCompositionRightUnitorIso C
  ; triangle-id = {!!} -- triangle-id
  ; pentagon-id = {!!} -- pentagon-id
  } where
    Fun = functorCategory C C
  
    _∘C_ = Category._∘_ C
    
    tensor = compositionFunctor C C C
    
    tensor₀ = Functor.F₀ tensor
    tensor₁ = Functor.F₁ tensor 
        
    unit : Obj Fun
    unit = Id[ C ]
    {-
    triangle-id : (x y : Obj Fun) 
                → tensor₁ (η (nat-trans right-unitor) x , id Fun)
                ≡ ⟨ tensor₁ (id Fun , η (nat-trans left-unitor) y) ⟩∘ᵥ⟨ η (nat-trans associator) (x ,' unit ,' y) ⟩
    triangle-id α β = {!!}
    
    pentagon-id : (w x y z : Obj Fun) 
                → ⟨ tensor₁ (id Fun , η (nat-trans associator) (x ,' y ,' z)) ⟩∘ᵥ⟨ ⟨ η (nat-trans associator) (w ,' tensor₀ (x , y) ,' z) ⟩∘ᵥ⟨ tensor₁ (η (nat-trans associator) (w ,' x ,' y) , id Fun) ⟩ ⟩
                ≡ ⟨ η (nat-trans associator) (w ,' x ,' tensor₀ (y , z)) ⟩∘ᵥ⟨ η (nat-trans associator) (tensor₀ (w , x) ,' y ,' z) ⟩
    pentagon-id w x y z = {!!}
-}
