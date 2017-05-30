
open import Level

open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Theory.Category
open import Theory.Functor

module Theory.Wedge.Definition where

open Category
open Functor renaming (id to functor-id ; compose to functor-compose)

--------------------------------------------------------------------------------
-- Definition of wedges
-- See: https://ncatlab.org/nlab/show/end#explicit_definition
--------------------------------------------------------------------------------

record Wedge {ℓC₀ ℓC₁ ℓX₀ ℓX₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {X : Category {ℓX₀} {ℓX₁}} (w : Obj X) (F : Functor (C op ×C C) X) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓX₁) where
  constructor wedge
  private
    _∘X_ = _∘_ X
  field
    e : (c : Obj C) → Hom X w (F₀ F (c , c))

    coher : {c c' : Obj C} (f : Hom C c c') 
          → F₁ F (f , id C {c'}) ∘X e c' ≡ F₁ F (id C {c} , f) ∘X e c 

  compose : {v : Obj X} → (f : Hom X v w) → Wedge v F
  compose {v} f = record 
    { e = λ c → e c ∘X f 
    ; coher = λ g → trans (assoc X) (trans (cong (λ Y → Y ∘X f) (coher g)) (sym (assoc X))) 
    }

--------------------------------------------------------------------------------
-- Definition of cowedges
-- See: https://ncatlab.org/nlab/show/end#explicit_definition
--------------------------------------------------------------------------------

record CoWedge {ℓC₀ ℓC₁ ℓX₀ ℓX₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {X : Category {ℓX₀} {ℓX₁}} (F : Functor (C op ×C C) X) (w : Obj X) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓX₁) where
  constructor cowedge
  private
    _∘X_ = _∘_ X
  field
    co-e : (c : Obj C) → Hom X (F₀ F (c , c)) w

    co-coher : {c c' : Obj C} (f : Hom C c c') 
          → co-e c' ∘X F₁ F (id C {c'} , f) ≡ co-e c ∘X F₁ F (f , id C {c}) 

  co-compose : {v : Obj X} → (f : Hom X w v) → CoWedge F v
  co-compose {v} f = record 
    { co-e = λ c → f ∘X co-e c  
    ; co-coher = λ g → trans (sym (assoc X)) (trans (cong (λ Y → f ∘X Y) (co-coher g)) (assoc X)) 
    } 
