
open import Level
open import Function

open import Data.Product

open import Theory.Category.Definition
open import Theory.Category.Examples
open import Theory.Functor.Definition

module Theory.Category.Concrete {ℓ ℓC₀ ℓC₁ : Level} where

-------------------------------------------------------------------------------
-- Definition of concrete categories
-------------------------------------------------------------------------------
IsConcreteCategory : (C : Category {ℓC₀} {ℓC₁}) → Set (suc ℓ ⊔ ℓC₀ ⊔ ℓC₁)
IsConcreteCategory C = Σ (Functor C (setCategory {ℓ})) IsFaithfulFunctor

ConcreteCategory : Set (suc (ℓ ⊔ ℓC₁ ⊔ ℓC₀))
ConcreteCategory = Σ (Category {ℓC₀} {ℓC₁}) IsConcreteCategory
