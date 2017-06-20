
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

open import Theory.End.DayConvolution

open import Extensionality

module Theory.Natural.Transformation.Examples.DayConvolutionAssociator where

open Category 

dayAssociator : {ℓC₀ ℓC₁ : Level} → (ℓSet : Level) → {C : Category {ℓC₀} {ℓC₁}} → (CMon : MonoidalCategory C)
              → NaturalTransformation (leftAssociator {C = [ C , setCategory {ℓSet ⊔ ℓC₀ ⊔ ℓC₁} ]} (dayConvolution {ℓSet = ℓSet} CMon)) 
                                      (rightAssociator {C = [ C , setCategory {ℓSet ⊔ ℓC₀ ⊔ ℓC₁} ]} (dayConvolution {ℓSet = ℓSet} CMon))
dayAssociator {ℓC₀} {ℓC₁} ℓSet {C} CMon = naturalTransformation η {!!}
  where
    dayConv = dayConvolution {ℓSet = ℓSet} CMon
    
    Set' = setCategory {ℓSet ⊔ ℓC₀ ⊔ ℓC₁}
    [C,S] = [ C , Set' ]
    
    lAssoc = leftAssociator {C = [C,S]} dayConv
    rAssoc = rightAssociator {C = [C,S]} dayConv
    
    η : (x : Obj ([C,S] ×C [C,S] ×C [C,S])) → Hom [C,S] ([ lAssoc ]₀ x) ([ rAssoc ]₀ x)
    η x = {!!}
