
open import Level

open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Utilities
open import Theory.Category
open import Theory.Functor
open import Theory.Wedge.Definition

module Theory.End.Definition where

open Category
open Functor renaming (id to functor-id ; compose to functor-compose)

--------------------------------------------------------------------------------
-- Definition of ends
-- See: https://ncatlab.org/nlab/show/end#explicit_definition
--------------------------------------------------------------------------------

record End {ℓC₀ ℓC₁ ℓX₀ ℓX₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {X : Category {ℓX₀} {ℓX₁}} (F : Functor (C op ×C C) X) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓX₀ ⊔ ℓX₁) where
  field
    w : Obj X
    e : Wedge w F
    universal : ∀ {w' : Obj X} (e' : Wedge w' F) → ∃ λ (f : Hom X w' w) → (IsUnique f) × (e' ≡ Wedge.compose e f)


--------------------------------------------------------------------------------
-- Definition of coends
-- See: https://ncatlab.org/nlab/show/end#explicit_definition
--------------------------------------------------------------------------------

record CoEnd {ℓC₀ ℓC₁ ℓX₀ ℓX₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {X : Category {ℓX₀} {ℓX₁}} (F : Functor (C op ×C C) X) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓX₀ ⊔ ℓX₁) where
  field
    co-w : Obj X
    co-e : CoWedge F co-w
    co-universal : ∀ {w' : Obj X} (e' : CoWedge F w') → ∃ λ (f : Hom X co-w w') → (IsUnique f) × (e' ≡ CoWedge.co-compose co-e f)
 
