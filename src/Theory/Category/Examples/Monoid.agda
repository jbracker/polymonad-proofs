
-- Stdlib
open import Level

open import Data.Unit hiding ( _≤_ )

open import Theory.Monoid
open import Theory.Category.Definition

module Theory.Category.Examples.Monoid where  

-- Category naturally formed by a monoid.
monoidCategory : {ℓ : Level} {C : Set ℓ} → Monoid C → Category {ℓ₀ = ℓ}
monoidCategory {ℓ = ℓ} monoid = record
  { Obj = Lift ⊤
  ; Hom = \_ _ → Monoid.carrier monoid
  ; _∘_ = Monoid._∙_ monoid
  ; id = Monoid.ε monoid
  ; assoc = Monoid.assoc monoid
  ; left-id = Monoid.right-id monoid
  ; right-id = Monoid.left-id monoid
  }
