
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ( [_] )
open ≡-Reasoning

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Category.Examples.SetCat using ( setCategory )
open import Theory.Category.Examples.Functor using ( [_,_] ) renaming ( functorCategory to FunCat )
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Association
open Theory.Functor.Association.Associator
open import Theory.Functor.Application
open Theory.Functor.Application.BiFunctor
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Properties
open import Theory.Natural.Isomorphism

open import Theory.End.DayConvolution
open import Theory.End.DayUnit

open import Theory.Category.Monoidal.Examples.FunctorWithDayConvolution.Postulates

open import Extensionality

module Theory.Category.Monoidal.Examples.FunctorWithDayConvolution.Postulates.TriangleId where

open Category
open Functor hiding ( id )
open NaturalIsomorphism renaming ( η to iso-η ) 

-- Agda does not seem to terminate in a reasonable amount of time...
-- Last tested with Agda 2.5.3
{- 
postulate
  day-triangle-id : {ℓC₀ ℓC₁ : Level} → (ℓSet : Level) → {C : Category {ℓC₀} {ℓC₁}} → (CMon : MonoidalCategory C) 
                  → (x y : Functor C (setCategory {ℓSet ⊔ ℓC₀ ⊔ ℓC₁})) 
                  → F₁ (dayConvolution {ℓSet = ℓSet} CMon) (iso-η (dayRightUnitor ℓSet CMon) x , id (FunCat C (setCategory {ℓSet ⊔ ℓC₀ ⊔ ℓC₁})) {y} )
                  ≡ ⟨ F₁ (dayConvolution {ℓSet = ℓSet} CMon) (id (FunCat C (setCategory {ℓSet ⊔ ℓC₀ ⊔ ℓC₁})) {x} , iso-η (dayLeftUnitor ℓSet CMon) y) ⟩∘ᵥ⟨ iso-η (dayAssociator ℓSet CMon) (x ,' dayUnit {ℓSet = ℓSet} CMon ,' y) ⟩
-}
