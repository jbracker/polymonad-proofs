
open import Level

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Bicategory
open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

module Theory.TwoCategory.Bicategory.Examples.FromMonoidalCategory where

open Category
open Functor hiding ( id )
open NaturalIsomorphism renaming ( η to nat-η )

MonoidalCategory→Bicategory : {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}}
                                   → MonoidalCategory C → Bicategory {zero} {ℓC₀} {ℓC₁}
MonoidalCategory→Bicategory {ℓC₀} {ℓC₁} {C} MC = record
  { Cell₀ = ⊤
  ; HomCat = λ _ _ → C
  ; id₁ = λ _ → MonoidalCategory.unit MC
  ; comp = MonoidalCategory.tensor MC
  ; left-unitor = MonoidalCategory.left-unitor MC
  ; right-unitor = MonoidalCategory.right-unitor MC
  ; associator = MonoidalCategory.associator MC
  ; triangle-id = λ f g → MonoidalCategory.triangle-id MC g f
  ; pentagon-id = λ f g h k → MonoidalCategory.pentagon-id MC k h g f
  }
