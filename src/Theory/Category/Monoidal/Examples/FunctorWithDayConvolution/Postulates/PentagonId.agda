
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

module Theory.Category.Monoidal.Examples.FunctorWithDayConvolution.Postulates.PentagonId where

open Category
open Functor hiding ( id )
open NaturalIsomorphism renaming ( η to iso-η ) 

-- Agda does not seem to terminate in a reasonable amount of time...
-- Last tested with Agda 2.5.3
{- 
postulate
  day-pentagon-id : {ℓC₀ ℓC₁ : Level} → (ℓSet : Level) → {C : Category {ℓC₀} {ℓC₁}} → (CMon : MonoidalCategory C) 
                  → (w x y z : Functor C (setCategory {ℓSet ⊔ ℓC₀ ⊔ ℓC₁})) 
                  → ⟨ F₁ (dayConvolution {ℓSet = ℓSet} CMon) (id [ C , setCategory {ℓSet ⊔ ℓC₀ ⊔ ℓC₁} ] , iso-η (dayAssociator ℓSet CMon) (x ,' y ,' z)) ⟩∘ᵥ⟨ 
                      ⟨ iso-η (dayAssociator ℓSet CMon) (w ,' F₀ (dayConvolution {ℓSet = ℓSet} CMon) (x , y) ,' z) ⟩∘ᵥ⟨ 
                        F₁ (dayConvolution {ℓSet = ℓSet} CMon) (iso-η (dayAssociator ℓSet CMon) (w ,' x ,' y) , id [ C , setCategory {ℓSet ⊔ ℓC₀ ⊔ ℓC₁} ]) ⟩ ⟩
                  ≡ ⟨ iso-η (dayAssociator ℓSet CMon) (w ,' x ,' F₀ (dayConvolution {ℓSet = ℓSet} CMon) (y , z)) ⟩∘ᵥ⟨ iso-η (dayAssociator ℓSet CMon) (F₀ (dayConvolution {ℓSet = ℓSet} CMon) (w , x) ,' y ,' z) ⟩
-}
