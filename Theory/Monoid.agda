 
module Theory.Monoid where

-- Stdlib
open import Level
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

-- Local
open import Theory.Category


record Monoid {ℓ} (C : Set ℓ) : Set ℓ where
  field
    ε : C
    _∙_ : C → C → C
    
    idR : {m : C} → m ∙ ε ≡ m
    idL : {m : C} → ε ∙ m ≡ m
    assoc : {m n o : C} → m ∙ (n ∙ o) ≡ (m ∙ n) ∙ o
  
  carrier : Set ℓ
  carrier = C

Monoid→Category : ∀ {ℓ} {C : Set ℓ} → Monoid C → Category {ℓ = ℓ}
Monoid→Category {ℓ = ℓ} monoid = record
  { Obj = Lift ⊤
  ; Hom = \_ _ → Monoid.carrier monoid
  ; _∘_ = Monoid._∙_ monoid
  ; id = Monoid.ε monoid
  ; assoc = Monoid.assoc monoid
  ; idL = Monoid.idL monoid
  ; idR = Monoid.idR monoid
  }
    
