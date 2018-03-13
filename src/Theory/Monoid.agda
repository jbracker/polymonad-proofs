 
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

record Monoid {ℓ} (C : Set ℓ) : Set ℓ where
  field
    ε : C
    _∙_ : C → C → C
    
    right-id : {m : C} → m ∙ ε ≡ m
    left-id : {m : C} → ε ∙ m ≡ m
    assoc : {m n o : C} → m ∙ (n ∙ o) ≡ (m ∙ n) ∙ o
  
  carrier : Set ℓ
  carrier = C
  
unitMonoid : Monoid ⊤
unitMonoid = record 
  { ε = tt 
  ; _∙_ = λ _ _ → tt 
  ; right-id = refl
  ; left-id = refl
  ; assoc = refl }
