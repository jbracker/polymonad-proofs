
-- Stdlib
open import Level

open import Data.Unit hiding ( _≤_ )

open import Relation.Binary.PropositionalEquality

open import Theory.Category.Definition

module Theory.Category.Examples.Codiscrete where  

-- Category that has exactly one morphism for any pair of objects.
codiscreteCategory : {ℓ : Level} → (A : Set ℓ) → Category {ℓ} {ℓ}
codiscreteCategory {ℓ} A = category A (λ a b → Lift ⊤) (λ _ _ → lift tt) (lift tt) refl refl refl
