
open import Level
open import Function

open import Data.Product

open import Theory.Category
open import Theory.Category.Examples
open import Theory.Functor

module Theory.Category.Concrete where

IsConcreteCategory : {ℓC₀ ℓC₁ ℓ : Level} → (C : Category {ℓC₀} {ℓC₁}) → Set (suc ℓ ⊔ ℓC₀ ⊔ ℓC₁)
IsConcreteCategory {ℓ = ℓ} C = Σ (Functor C (setCategory {ℓ})) IsFaithfulFunctor

