
module Theory.Natural.DinaturalTransformation where

-- Stdlib
open import Level
open import Function hiding ( _∘_ ; id )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality
  renaming ( sym to hsym ; trans to htrans ; cong to hcong ; subst₂ to hsubst₂ ; proof-irrelevance to hproof-irrelevance )
open ≡-Reasoning 

-- Local
open import Utilities
open import Theory.Category
open import Theory.Functor

open Category
open Functor hiding ( id )

-------------------------------------------------------------------------------
-- Definition of Natural Transformations
-------------------------------------------------------------------------------

-- Definition is based on: https://ncatlab.org/nlab/show/dinatural+transformation
record DinaturalTransformation {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                             {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                             (F : Functor (C op ×C C) D) (G : Functor (C op ×C C) D) 
                             : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  constructor dinaturalTransformation
  private _∘D_ = Category._∘_ D
  field
    α : (c : Obj C) → Hom D ([ F ]₀ (c , c)) ([ G ]₀ (c , c))
    
    dinatural : {a b : Obj C} {f : Hom C a b} 
              → [ G ]₁ (id C {a} , f) ∘D (α a ∘D ([ F ]₁ (f , id C {a}))) ≡ [ G ]₁ (f , id C {b}) ∘D (α b ∘D [ F ]₁ (id C {b} , f))
